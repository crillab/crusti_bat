use super::dimacs_common;
use crate::{core::BeliefRevisionProblem, CNFFormula, Variable, Weighted};
use anyhow::{anyhow, Context, Result};
use std::{
    cell::RefCell,
    io::{BufRead, BufReader, Read},
    rc::Rc,
    str::SplitWhitespace,
};

#[derive(Default)]
pub struct BeliefRevisionDimacsReader;

impl BeliefRevisionDimacsReader {
    pub fn read<R>(&self, reader: R) -> Result<BeliefRevisionProblem>
    where
        R: Read,
    {
        let mut r = BufReader::new(reader);
        let mut buffer = String::new();
        let context = "while parsing a belief revision DIMACS instance";
        let line_index = Rc::new(RefCell::new(0));
        let line_index_context = || format!("while parsing line at index {}", line_index.borrow());
        let mut preamble_data = None;
        let mut topics = Vec::new();
        let mut revision_formula = None;
        let mut initial_formula = None;
        loop {
            let line = r.read_line(&mut buffer)?;
            if line == 0 {
                break;
            }
            let mut words = buffer.split_whitespace();
            if let Some(first_word) = words.next() {
                match first_word {
                    "c" => {}
                    "p" => dimacs_common::read_preamble(
                        &mut words,
                        &mut preamble_data,
                        "the number of topics",
                    )
                    .context("while reading the preamble")
                    .with_context(line_index_context)
                    .context(context)?,
                    "t" => {
                        dimacs_common::assert_preamble_is_present(&preamble_data)?;
                        if revision_formula.is_some() {
                            return Err(anyhow!("cannot declare topics after clauses"))
                                .with_context(line_index_context)
                                .context(context);
                        }
                        topics.push(
                            read_topic(&mut words, preamble_data.unwrap().0)
                                .context("while reading a topic")
                                .with_context(line_index_context)
                                .context(context)?,
                        )
                    }
                    "s" => {
                        dimacs_common::assert_preamble_is_present(&preamble_data)?;
                        if initial_formula.is_some() {
                            return Err(anyhow!(r#"multiple "s" lines"#))
                                .with_context(line_index_context)
                                .context(context);
                        }
                        let n = dimacs_common::expect_usize(&mut words, r#""1""#)
                            .with_context(line_index_context)
                            .context(context)?;
                        if n != 1 {
                            return Err(anyhow!(r#"expected "1", got"{}""#, n))
                                .with_context(line_index_context)
                                .context(context);
                        }
                        initial_formula = Some(CNFFormula::default());
                        initial_formula
                            .as_mut()
                            .unwrap()
                            .add_vars(preamble_data.unwrap().0);
                    }
                    s => {
                        if let Ok(l) = str::parse::<isize>(s) {
                            dimacs_common::assert_preamble_is_present(&preamble_data)?;
                            let clause =
                                dimacs_common::read_clause(&mut words, l, preamble_data.unwrap().0)
                                    .context("while reading a clause")
                                    .with_context(line_index_context)
                                    .context(context)?;
                            if revision_formula.is_none() {
                                revision_formula = Some(CNFFormula::default());
                                revision_formula
                                    .as_mut()
                                    .unwrap()
                                    .add_vars(preamble_data.unwrap().0);
                            }
                            if initial_formula.is_some() {
                                initial_formula.as_mut().unwrap().add_clause(clause);
                            } else {
                                revision_formula.as_mut().unwrap().add_clause(clause);
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
        dimacs_common::assert_preamble_is_present(&preamble_data)?;
        let (n_vars, n_topics) = preamble_data.unwrap();
        if topics.len() != n_topics {
            return Err(anyhow!("less topic definitions than expected")).context(context);
        }
        if initial_formula.is_none() {
            return Err(anyhow!(r#"no "s" line"#)).context(context);
        }
        Ok(BeliefRevisionProblem::new(
            n_vars,
            topics,
            revision_formula.unwrap(),
            initial_formula.unwrap(),
        ))
    }
}

fn read_topic(words: &mut SplitWhitespace, n_vars: usize) -> Result<Weighted<Vec<Variable>>> {
    let weight = dimacs_common::expect_usize(words, "a weight as second word")?;
    let topic_vars = words
        .map_while(|w| {
            let v = match dimacs_common::expect_usize(&mut std::iter::once(w), "a variable index") {
                Ok(v) => v,
                Err(e) => return Some(Err(e)),
            };
            if v == 0 {
                None
            } else if v > n_vars {
                Some(Err(anyhow!(
                    "variable index {} is higher than the number of variables",
                    v
                )))
            } else {
                Some(Ok(v))
            }
        })
        .collect::<Result<Vec<Variable>>>()?;
    dimacs_common::expect_eol(words, "something after 0")?;
    Ok(Weighted::new(topic_vars, weight))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CNFDimacsWriter;
    use std::io::BufWriter;

    #[test]
    fn test_empty_instance() {
        let content = "";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_unknown_first_word() {
        let content = "a cnf 0 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_error_cnf() {
        let content = "p dnf 0 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_error_n_vars() {
        let content = "p cnf a 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_error_n_belief_bases() {
        let content = "p cnf 0 a\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_1() {
        let content = "p\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_2() {
        let content = "p cnf\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_3() {
        let content = "p cnf 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_len_is_5() {
        let content = "p cnf 0 0 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_preamble_twice() {
        let content = "p cnf 0 0\np cnf 0 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_no_preamble() {
        let content = "w 1 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_not_a_var() {
        let content = "p cnf 1 0\nw a 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_var_index_too_high() {
        let content = "p cnf 1 0\nw 2 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_not_a_weight() {
        let content = "p cnf 1 0\nw 1 a\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_len_is_1() {
        let content = "p cnf 1 0\nw\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_len_is_2() {
        let content = "p cnf 1 0\nw 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_len_is_4() {
        let content = "p cnf 1 0\nw 1 1 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_weight_multiple_definition() {
        let content = "p cnf 1 0\nw 1 1\nw 1 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_not_a_lit() {
        let content = "p cnf 1 0\na 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_first_var_index_too_high() {
        let content = "p cnf 1 0\n2 1 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_second_var_index_too_high() {
        let content = "p cnf 1 0\n1 2 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_missing_zero() {
        let content = "p cnf 1 0\n1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_integrity_clause_content_after_0() {
        let content = "p cnf 1 0\n1 0 1 0\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_too_much_belief_base_weights() {
        let content = "p cnf 1 1\ns 1\ns 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_weight_in_not_a_weight() {
        let content = "p cnf 1 1\ns a\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_weight_len_is_1() {
        let content = "p cnf 1 1\ns\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_weight_len_is_3() {
        let content = "p cnf 1 1\ns 1 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_belief_base_some_are_undef() {
        let content = "p cnf 1 1\n";
        let reader = BeliefRevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    fn assert_cnf_eq(expected: &str, actual: &CNFFormula) {
        let mut writer = BufWriter::new(Vec::new());
        CNFDimacsWriter.write(&mut writer, actual).unwrap();
        assert_eq!(
            expected,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_ok() {
        let content = r#"
p cnf 3 4
t 16 1 2 3 0
t 2 1 0
t 4 2 0
t 8 3 0
3 0
1 2 0
s 1
-1 2 0
1 -2 0
-2 -3 0
2 3 0
"#;
        let reader = BeliefRevisionDimacsReader;
        let problem = reader.read(content.as_bytes()).unwrap();
        assert_eq!(3, problem.n_vars());
        assert_eq!(
            &[
                Weighted::new(vec![1, 2, 3], 16),
                Weighted::new(vec![1], 2),
                Weighted::new(vec![2], 4),
                Weighted::new(vec![3], 8),
            ],
            problem.topics()
        );
        assert_cnf_eq("p cnf 3 2\n3 0\n1 2 0\n", problem.revision_formula());
        assert_cnf_eq(
            "p cnf 3 4\n-1 2 0\n1 -2 0\n-2 -3 0\n2 3 0\n",
            problem.initial_formula(),
        );
    }
}
