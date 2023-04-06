use anyhow::{anyhow, Context, Result};
use rustc_hash::FxHashMap;
use std::{
    cell::RefCell,
    collections::hash_map::Entry,
    io::{BufRead, BufReader, Read},
    rc::Rc,
    str::SplitWhitespace,
};
use crate::{CNFFormula, Clause, MergingProblem, Variable, Weighted};

#[derive(Default)]
pub struct MergingDimacsReader;

impl MergingDimacsReader {
    pub fn read<R>(&self, reader: R) -> Result<MergingProblem>
    where
        R: Read,
    {
        let mut r = BufReader::new(reader);
        let mut buffer = String::new();
        let context = "while parsing a merging DIMACS instance";
        let line_index = Rc::new(RefCell::new(0));
        let line_index_context = || format!("while parsing line at index {}", line_index.borrow());
        let mut preamble_data = None;
        let mut var_weights = FxHashMap::default();
        let mut integrity_clauses = Vec::new();
        let mut belief_bases_weights = Vec::new();
        let mut belief_bases_constraints = Vec::new();
        loop {
            let line = r.read_line(&mut buffer)?;
            if line == 0 {
                break;
            }
            let mut words = buffer.split_whitespace();
            if let Some(first_word) = words.next() {
                match first_word {
                    "c" => {}
                    "p" => read_preamble(&mut words, &mut preamble_data)
                        .context("while reading the preamble")
                        .with_context(line_index_context)
                        .context(context)?,
                    "w" => {
                        assert_preamble_is_present(&preamble_data)?;
                        read_var_weight(&mut words, preamble_data.unwrap().0, &mut var_weights)
                            .context("while reading a variable weight")
                            .with_context(line_index_context)
                            .context(context)?
                    }
                    "s" => {
                        assert_preamble_is_present(&preamble_data)?;
                        if belief_bases_weights.len() == preamble_data.unwrap().1 {
                            return Err(anyhow!("more belief base definitions than expected"))
                                .with_context(line_index_context)
                                .context(context);
                        }
                        let w = read_belief_base_weight(&mut words)
                            .context("while reading a belief base weight")
                            .with_context(line_index_context)
                            .context(context)?;
                        belief_bases_weights.push(w);
                        belief_bases_constraints.push(Vec::new());
                    }
                    s => {
                        if let Ok(l) = str::parse::<isize>(s) {
                            assert_preamble_is_present(&preamble_data)?;
                            let clause = read_clause(&mut words, l, preamble_data.unwrap().0)
                                .context("while reading a clause")
                                .with_context(line_index_context)
                                .context(context)?;
                            match belief_bases_constraints.last_mut() {
                                Some(clauses) => clauses.push(clause),
                                None => integrity_clauses.push(clause),
                            }
                        } else {
                            return Err(anyhow!(r#"unexpected first word "{}""#, first_word))
                                .with_context(line_index_context)
                                .context(context);
                        }
                    }
                }
            }
            buffer.clear();
            *line_index.borrow_mut() += 1;
        }
        assert_preamble_is_present(&preamble_data)?;
        let (n_vars, n_belief_bases) = preamble_data.unwrap();
        if belief_bases_weights.len() != n_belief_bases {
            return Err(anyhow!("less belief base definitions than expected")).context(context);
        }
        let mut var_weights_vec: Vec<Weighted<Variable>> = var_weights
            .into_iter()
            .map(|e| Weighted::new(e.0, e.1))
            .collect();
        var_weights_vec.sort_unstable_by_key(|w| *w.thing());
        Ok(MergingProblem::new(
            n_vars,
            var_weights_vec,
            CNFFormula::new_from_clauses_unchecked(n_vars, integrity_clauses),
            belief_bases_constraints
                .into_iter()
                .enumerate()
                .map(|(i, clauses)| {
                    Weighted::new(
                        CNFFormula::new_from_clauses_unchecked(n_vars, clauses),
                        belief_bases_weights[i],
                    )
                })
                .collect(),
        ))
    }
}

fn expect_usize(words: &mut SplitWhitespace, what: &str) -> Result<usize> {
    match words.next() {
        Some(s) => match str::parse::<usize>(s) {
            Ok(n) => Ok(n),
            Err(_) => Err(anyhow!(r#"expected {}, got "{}""#, what, s)),
        },
        None => Err(anyhow!(r#"expected {}, got end of line"#, what)),
    }
}

fn expect_eol(words: &mut SplitWhitespace, what: &str) -> Result<()> {
    if let Some(s) = words.next() {
        Err(anyhow!(r#"expected end of line, got {} "{}""#, s, what))
    } else {
        Ok(())
    }
}

fn read_preamble(
    words: &mut SplitWhitespace,
    preamble_data: &mut Option<(usize, usize)>,
) -> Result<()> {
    if preamble_data.is_some() {
        return Err(anyhow!("got a second preamble line"));
    }
    match words.next() {
        Some("cnf") => Ok(()),
        Some(s) => Err(anyhow!(r#"expected "cnf" as second word, got "{}""#, s)),
        None => Err(anyhow!(r#"expected "cnf", got end of line"#)),
    }?;
    let n_vars = expect_usize(words, "a number of variables as third word")?;
    let n_belief_bases = expect_usize(words, "the number of belief bases as fourth word")?;
    expect_eol(words, "a fifth word")?;
    *preamble_data = Some((n_vars, n_belief_bases));
    Ok(())
}

fn assert_preamble_is_present(preamble_data: &Option<(usize, usize)>) -> Result<()> {
    if preamble_data.is_none() {
        Err(anyhow!("preamble has not been defined"))
    } else {
        Ok(())
    }
}

fn read_var_weight(
    words: &mut SplitWhitespace,
    n_vars: usize,
    var_weights: &mut FxHashMap<usize, usize>,
) -> Result<()> {
    let var_index = expect_usize(words, "a variable index as second word")?;
    if var_index > n_vars {
        return Err(anyhow!(
            "variable index {} is higher than the number of variables",
            var_index
        ));
    }
    let weight = expect_usize(words, "a weight as third word")?;
    expect_eol(words, "a fourth word")?;
    match var_weights.entry(var_index) {
        Entry::Occupied(_) => {
            return Err(anyhow!(
                "multiple definition of the weight for variable {}",
                var_index
            ));
        }
        Entry::Vacant(e) => {
            e.insert(weight);
        }
    }
    Ok(())
}

fn expect_literal_or_zero(words: &mut SplitWhitespace, n_vars: usize) -> Result<isize> {
    match words.next() {
        Some(word) => match str::parse::<isize>(word) {
            Ok(n) => {
                if n.abs() as usize <= n_vars {
                    Ok(n)
                } else {
                    Err(anyhow!(
                        r#"literal {} has a variable index higher than the number of variables"#,
                        n
                    ))
                }
            }
            Err(_) => Err(anyhow!(r#"expected a literal, got "{}""#, word)),
        },
        None => Err(anyhow!(r#"expected a literal or 0, got end of line"#)),
    }
}

fn read_clause(words: &mut SplitWhitespace, first_lit: isize, n_vars: usize) -> Result<Clause> {
    let mut clause = Vec::new();
    match first_lit {
        n if n.abs() as usize > n_vars => {
            return Err(anyhow!(
                r#"literal {} has a variable index higher than the number of variables"#,
                first_lit
            ))
        }
        0 => return Ok(clause),
        n => clause.push(n),
    }
    loop {
        let l = expect_literal_or_zero(words, n_vars)?;
        if l == 0 {
            break;
        }
        clause.push(l);
    }
    expect_eol(words, "something after 0")?;
    Ok(clause)
}

fn read_belief_base_weight(words: &mut SplitWhitespace) -> Result<usize> {
    let weight = expect_usize(words, "a weight as second word")?;
    expect_eol(words, "a third word")?;
    Ok(weight)
}

#[cfg(test)]
mod tests {
    use std::io::BufWriter;

    use super::*;

    #[test]
    fn test_empty_instance() {
        let content = "";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_unknown_first_word() {
        let content = "a cnf 0 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_error_cnf() {
        let content = "p dnf 0 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_error_n_vars() {
        let content = "p cnf a 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_error_n_belief_bases() {
        let content = "p cnf 0 a\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_1() {
        let content = "p\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_2() {
        let content = "p cnf\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_3() {
        let content = "p cnf 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_5() {
        let content = "p cnf 0 0 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_twice() {
        let content = "p cnf 0 0\np cnf 0 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_no_preamble() {
        let content = "w 1 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_not_a_var() {
        let content = "p cnf 1 0\nw a 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_var_index_too_high() {
        let content = "p cnf 1 0\nw 2 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_not_a_weight() {
        let content = "p cnf 1 0\nw 1 a\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_len_is_1() {
        let content = "p cnf 1 0\nw\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_len_is_2() {
        let content = "p cnf 1 0\nw 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_len_is_4() {
        let content = "p cnf 1 0\nw 1 1 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_multiple_definition() {
        let content = "p cnf 1 0\nw 1 1\nw 1 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_not_a_lit() {
        let content = "p cnf 1 0\na 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_first_var_index_too_high() {
        let content = "p cnf 1 0\n2 1 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_second_var_index_too_high() {
        let content = "p cnf 1 0\n1 2 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_missing_zero() {
        let content = "p cnf 1 0\n1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_content_after_0() {
        let content = "p cnf 1 0\n1 0 1 0\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_too_much_belief_base_weights() {
        let content = "p cnf 1 1\ns 1\ns 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_weight_in_not_a_weight() {
        let content = "p cnf 1 1\ns a\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_weight_len_is_1() {
        let content = "p cnf 1 1\ns\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_weight_len_is_3() {
        let content = "p cnf 1 1\ns 1 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_some_are_undef() {
        let content = "p cnf 1 1\n";
        let reader = MergingDimacsReader::default();
        assert!(reader.read(content.as_bytes()).is_err());
    }

    fn assert_cnf_eq(expected: &str, actual: &CNFFormula) {
        let mut writer = BufWriter::new(Vec::new());
        actual.to_dimacs(&mut writer).unwrap();
        assert_eq!(
            expected,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_ok() {
        let content = r#"
p cnf 3 2
w 1 0
w 3 2
w 2 1
-1 2 0
-2 3 0
s 1
-1 -2 0
1 2 0
s 2
-1 -3 0
1 3 0
"#;
        let reader = MergingDimacsReader::default();
        let problem = reader.read(content.as_bytes()).unwrap();
        assert_eq!(3, problem.n_vars());
        assert_eq!(
            &[
                Weighted::new(1, 0),
                Weighted::new(2, 1),
                Weighted::new(3, 2)
            ],
            problem.var_weights()
        );
        assert_cnf_eq(
            "p cnf 3 2\n-1 2 0\n-2 3 0\n",
            problem.integrity_constraint(),
        );
        assert_eq!(2, problem.belief_bases().len());
        assert_eq!(1, problem.belief_bases()[0].weight());
        assert_cnf_eq(
            "p cnf 3 2\n-1 -2 0\n1 2 0\n",
            problem.belief_bases()[0].thing(),
        );
        assert_eq!(2, problem.belief_bases()[1].weight());
        assert_cnf_eq(
            "p cnf 3 2\n-1 -3 0\n1 3 0\n",
            problem.belief_bases()[1].thing(),
        );
    }
}
