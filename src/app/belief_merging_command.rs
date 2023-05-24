use anyhow::{anyhow, Context, Result};
use crusti_app_helper::{debug, info, App, AppSettings, Arg, ArgMatches, Command, SubCommand};
use crusti_bat::{
    CNFDimacsWriter, CNFFormula, Clause, DiscrepancyEncoding, DistanceEncoding,
    DrasticDistanceEncoding, HammingDistanceEncoding, MaxSatEncoding, MergingDimacsReader,
    SumAggregatorEncoding, ToCNFFormula, VarWeights, WCNFDimacs2022Writer, Weighted,
};
use std::{
    fs::{self, File},
    io::{BufRead, BufReader, BufWriter, Write},
    path::PathBuf,
    process::{self, Output},
    str::SplitWhitespace,
};
use tempfile::Builder;

const CMD_NAME: &str = "belief-merging";

const ARG_INPUT: &str = "ARG_INPUT";
const ARG_DISTANCE: &str = "ARG_DISTANCE";
const ARG_SOLVER: &str = "ARG_SOLVER";

#[derive(Default)]
pub(crate) struct BeliefMergingCommand;

impl<'a> Command<'a> for BeliefMergingCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Merge belief bases")
            .setting(AppSettings::DisableVersion)
            .arg(
                Arg::with_name(ARG_INPUT)
                    .short("i")
                    .long("input")
                    .empty_values(false)
                    .multiple(false)
                    .help("the input file that contains the formulas to merge")
                    .required(true),
            )
            .arg(
                Arg::with_name(ARG_DISTANCE)
                    .short("d")
                    .long("distance")
                    .empty_values(false)
                    .multiple(false)
                    .possible_values(&["drastic", "hamming"])
                    .help("the metrics used for distances")
                    .required(true),
            )
            .arg(
                Arg::with_name(ARG_SOLVER)
                    .short("s")
                    .long("solver")
                    .empty_values(false)
                    .multiple(false)
                    .help("the path to the MaxSAT solver")
                    .required(true),
            )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let reader = MergingDimacsReader::default();
        let file_path = arg_matches.value_of(ARG_INPUT).unwrap();
        let input_file_canonicalized = fs::canonicalize(PathBuf::from(file_path))
            .with_context(|| format!(r#"while opening file "{}""#, file_path))?;
        info!("reading input file {:?}", input_file_canonicalized);
        let file_reader = BufReader::new(File::open(input_file_canonicalized)?);
        let input_data = reader.read(file_reader)?;
        let (belief_bases, belief_bases_weights): (Vec<_>, Vec<_>) = input_data
            .belief_bases()
            .iter()
            .map(|w| (w.thing(), w.weight()))
            .unzip();
        let discrepancy_encoding =
            DiscrepancyEncoding::new(input_data.integrity_constraint(), &belief_bases);
        let distance_encoding =
            create_distance_encoding(arg_matches, &discrepancy_encoding, input_data.var_weights());
        let sum_aggregator_encoding =
            SumAggregatorEncoding::new(distance_encoding.as_ref(), &belief_bases_weights);
        let wcnf_hard = sum_aggregator_encoding.to_cnf_formula();
        let wcnf_soft = sum_aggregator_encoding.soft_clauses();
        let optimum = execute_maxsat(
            arg_matches.value_of(ARG_SOLVER).unwrap(),
            &wcnf_hard,
            &wcnf_soft,
        )
        .context("while solving a MaxSAT problem")?;
        let enforced_cnf = sum_aggregator_encoding.enforce_value(optimum);
        let cnf_writer = CNFDimacsWriter::default();
        cnf_writer.write(&mut std::io::stdout(), &enforced_cnf)
    }
}

fn create_distance_encoding<'a>(
    arg_matches: &ArgMatches<'_>,
    discrepancy_encoding: &'a DiscrepancyEncoding,
    var_weights: &'a VarWeights,
) -> Box<dyn DistanceEncoding + 'a> {
    match arg_matches.value_of(ARG_DISTANCE).unwrap() {
        "drastic" => Box::new(DrasticDistanceEncoding::new(
            discrepancy_encoding,
            var_weights,
        )),
        "hamming" => Box::new(HammingDistanceEncoding::new(
            discrepancy_encoding,
            var_weights,
        )),
        _ => unreachable!(),
    }
}

fn execute_maxsat(
    solver_path: &str,
    wcnf_hard: &CNFFormula,
    wcnf_soft: &[Weighted<Clause>],
) -> Result<usize> {
    let wcnf_writer = WCNFDimacs2022Writer::default();
    let (mut wcnf_file, wcnf_file_path) = Builder::new()
        .prefix("crusti_bat-")
        .suffix(".wcnf")
        .tempfile()
        .context("while creating a temporary file")?
        .keep()
        .context("while cancelling the temporary file deletion")?;
    debug!("writing the MaxSAT problem into {:?}", wcnf_file_path);
    let mut wcnf_file_writer = BufWriter::new(&mut wcnf_file);
    wcnf_writer
        .write(&mut wcnf_file_writer, wcnf_hard, wcnf_soft)
        .context("while writing the MaxSAT problem")?;
    wcnf_file_writer.flush().unwrap();
    std::mem::drop(wcnf_file_writer);
    std::mem::drop(wcnf_file);
    let command_output = process::Command::new(solver_path)
        .arg(format!("{}", wcnf_file_path.display()))
        .output()
        .context("while invoking the external MaxSAT solver")?;
    let optimum = extract_maxsat_output(&command_output)?;
    info!(
        "MaxSAT solver exited successfully with an optimal value of {}",
        optimum
    );
    fs::remove_file(wcnf_file_path).context("while deleting the temporary file")?;
    Ok(optimum)
}

fn extract_maxsat_output(out: &Output) -> Result<usize> {
    let context = "while inspecting the output of the MaxSAT solver";
    if !out.status.success() {
        return Err(anyhow!("MaxSAT solver ended with an error status")).context(context);
    }
    let mut out_reader = BufReader::new(out.stdout.as_slice());
    let mut s_line = None;
    let mut o_line = None;
    let update_line = |l: &mut Option<String>, words: SplitWhitespace| {
        if l.is_some() {
            return Err(anyhow!(r#"multiple "s" lines in output"#)).context(context);
        }
        *l = Some(words.into_iter().fold(String::new(), |mut acc, x| {
            if !acc.is_empty() {
                acc.push(' ');
            }
            acc.push_str(x);
            acc
        }));
        Ok(())
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
                        "c" | "v" => continue,
                        "s" => update_line(&mut s_line, words).context(context)?,
                        "o" => update_line(&mut o_line, words).context(context)?,
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
    let o = o_line.ok_or(anyhow!(r#"missing "o" line"#).context(context))?;
    str::parse::<usize>(&o)
        .context("while reading the final objective value")
        .context(context)
}
