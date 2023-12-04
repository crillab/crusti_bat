use super::Clause;
use crate::{io::WCNFDimacs2022Writer, CNFFormula, Weighted};
use anyhow::{anyhow, Context, Result};
use std::{
    fs,
    io::{BufRead, BufReader, BufWriter, Write},
    path::PathBuf,
    process::{self, Output},
    str::SplitWhitespace,
};
use tempfile::Builder;

/// An interface for MaxSAT solvers.
pub trait MaxSatSolver {
    fn solve(
        &self,
        wcnf_hard: &CNFFormula,
        wcnf_soft: &[Weighted<Clause>],
    ) -> Result<(usize, Vec<isize>)>;
}

/// An external MaxSAT solver, built thanks to the path to its executable.
/// The solver must follow the I/O rules defined by the MaxSAT Evaluation 2023.
pub struct ExternalMaxSatSolver(PathBuf);

impl MaxSatSolver for ExternalMaxSatSolver {
    fn solve(
        &self,
        wcnf_hard: &CNFFormula,
        wcnf_soft: &[Weighted<Clause>],
    ) -> Result<(usize, Vec<isize>)> {
        let wcnf_writer = WCNFDimacs2022Writer;
        let (mut wcnf_file, wcnf_file_path) = Builder::new()
            .prefix("crusti_bat-")
            .suffix(".wcnf")
            .tempfile()
            .context("while creating a temporary file")?
            .keep()
            .context("while cancelling the temporary file deletion")?;
        let mut wcnf_file_writer = BufWriter::new(&mut wcnf_file);
        wcnf_writer
            .write(&mut wcnf_file_writer, wcnf_hard, wcnf_soft)
            .context("while writing the MaxSAT problem")?;
        wcnf_file_writer.flush().unwrap();
        std::mem::drop(wcnf_file_writer);
        std::mem::drop(wcnf_file);
        let command_output = process::Command::new(&self.0)
            .arg(format!("{}", wcnf_file_path.display()))
            .output()
            .context("while invoking the external MaxSAT solver")?;
        let optimum = extract_maxsat_output(&command_output)?;
        fs::remove_file(wcnf_file_path).context("while deleting the temporary file")?;
        Ok(optimum)
    }
}

fn extract_maxsat_output(out: &Output) -> Result<(usize, Vec<isize>)> {
    if !out.status.success() {
        return Err(anyhow!("MaxSAT solver ended with an error status"))
            .context("while inspecting the output of the MaxSAT solver");
    }
    let out_reader = BufReader::new(out.stdout.as_slice());
    extract_maxsat_output_content(out_reader)
}

fn extract_maxsat_output_content(mut out_reader: BufReader<&[u8]>) -> Result<(usize, Vec<isize>)> {
    let context = "while inspecting the output of the MaxSAT solver";
    let mut s_line = None;
    let mut o_line = None;
    let mut v_line = Vec::new();
    let update_line = |l: &mut Option<String>, words: SplitWhitespace| {
        *l = Some(words.into_iter().fold(String::new(), |mut acc, x| {
            if !acc.is_empty() {
                acc.push(' ');
            }
            acc.push_str(x);
            acc
        }));
    };
    let mut buffer = String::new();
    loop {
        buffer.clear();
        match out_reader.read_line(&mut buffer) {
            Ok(0) => break,
            Err(e) => return Err(e).context(context),
            Ok(_) => {
                let mut words = buffer.split_whitespace();
                match words.next() {
                    Some(w) => match w {
                        "c" => continue,
                        "v" => {
                            v_line.append(
                                &mut words
                                    .map(|w| {
                                        str::parse::<isize>(w).context("while parsing a v-line")
                                    })
                                    .collect::<Result<_>>()?,
                            );
                        }
                        "s" => {
                            if s_line.is_some() {
                                return Err(anyhow!(r#"multiple "s" lines in output"#))
                                    .context(context);
                            }
                            update_line(&mut s_line, words)
                        }
                        "o" => update_line(&mut o_line, words),
                        _ => {
                            return Err(anyhow!(r#"unexpected line: "{}""#, buffer))
                                .context(context)
                        }
                    },
                    None => continue,
                }
            }
        }
    }
    let s = s_line.ok_or(anyhow!(r#"missing "s" line"#).context(context))?;
    if s != "OPTIMUM FOUND" {
        return Err(anyhow!(
            r#"wrong solver status; expected "OPTIMUM FOUND", got "{}""#,
            s
        ));
    }
    let o = str::parse::<usize>(&o_line.ok_or(anyhow!(r#"missing "o" line"#).context(context))?)
        .context("while reading the final objective value")
        .context(context)?;
    Ok((o, v_line))
}

impl From<PathBuf> for ExternalMaxSatSolver {
    fn from(value: PathBuf) -> Self {
        Self(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_maxsat_output_multiple_o_lines() {
        let output = "o 3\no 2\ns OPTIMUM FOUND\n";
        assert_eq!(
            2,
            extract_maxsat_output_content(BufReader::new(output.as_bytes()))
                .unwrap()
                .0
        )
    }

    #[test]
    fn test_maxsat_output_multiple_s_lines() {
        let output = "o 3\no 2\ns OPTIMUM FOUND\ns OPTIMUM FOUND\n";
        assert!(extract_maxsat_output_content(BufReader::new(output.as_bytes())).is_err())
    }
}
