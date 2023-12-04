use crate::{
    core::{Clause, MergingProblem, RevisionProblem, VarWeights, Variable},
    CNFFormula, Weighted,
};
use anyhow::{anyhow, Context, Result};
use rustc_hash::FxHashMap;
use std::{
    cell::RefCell,
    collections::hash_map::Entry,
    io::{BufRead, BufReader, Read},
    rc::Rc,
    str::SplitWhitespace,
};

/// A structure used to read the merging-related DIMACS-like format used by bm2cnf.
#[derive(Default)]
pub struct MergingDimacsReader;

impl MergingDimacsReader {
    /// Parses a belief merging instance.
    pub fn read<R>(&self, reader: R) -> Result<MergingProblem>
    where
        R: Read,
    {
        let mut dimacs_reader = DimacsReader {
            preamble_data: None,
            weights_type: WeightsType::VarWeightsMap(FxHashMap::default()),
            first_formula: CNFFormula::default(),
            belief_bases: BeliefBasesHandler {
                weights: Vec::new(),
                constraints: Vec::new(),
                single_base: false,
            },
        };
        dimacs_reader
            .read(reader)
            .context("while parsing a merging DIMACS instance")?;
        let DimacsReader {
            preamble_data: pd,
            weights_type: wt,
            first_formula: ff,
            belief_bases: bb,
        } = dimacs_reader;
        let n_vars = pd.unwrap().0;
        let mut var_weights = VarWeights::new(n_vars);
        wt.unwrap_var_weights_map()
            .into_iter()
            .for_each(|(v, w)| var_weights.add(Weighted::new(v, w)));
        Ok(MergingProblem::new(
            n_vars,
            var_weights,
            ff,
            bb.into_cnf_vec(n_vars),
        ))
    }
}

/// A structure used to read the revision-related DIMACS-like format used by br2cnf.
#[derive(Default)]
pub struct RevisionDimacsReader;

impl RevisionDimacsReader {
    /// Parses a belief revision instance.
    pub fn read<R>(&self, reader: R) -> Result<RevisionProblem>
    where
        R: Read,
    {
        let mut dimacs_reader = DimacsReader {
            preamble_data: None,
            weights_type: WeightsType::TopicWeights(Vec::new()),
            first_formula: CNFFormula::default(),
            belief_bases: BeliefBasesHandler {
                weights: Vec::new(),
                constraints: Vec::new(),
                single_base: true,
            },
        };
        dimacs_reader
            .read(reader)
            .context("while parsing a merging DIMACS instance")?;
        let DimacsReader {
            preamble_data: pd,
            weights_type: wt,
            first_formula: ff,
            belief_bases: bb,
        } = dimacs_reader;
        let n_vars = pd.unwrap().0;
        Ok(RevisionProblem::new(
            n_vars,
            ff,
            bb.into_cnf_vec(n_vars).pop().unwrap().into_thing(),
            wt.unwrap_topics(),
        ))
    }
}

struct DimacsReader {
    preamble_data: Option<(usize, usize)>,
    weights_type: WeightsType,
    first_formula: CNFFormula,
    belief_bases: BeliefBasesHandler,
}

enum WeightsType {
    VarWeightsMap(FxHashMap<usize, usize>),
    TopicWeights(Vec<Weighted<Vec<Variable>>>),
}

impl WeightsType {
    fn unwrap_var_weights_map(self) -> FxHashMap<usize, usize> {
        if let Self::VarWeightsMap(vwm) = self {
            vwm
        } else {
            panic!()
        }
    }

    fn unwrap_topics(self) -> Vec<Weighted<Vec<Variable>>> {
        if let Self::TopicWeights(tw) = self {
            tw
        } else {
            panic!()
        }
    }
}

struct BeliefBasesHandler {
    weights: Vec<usize>,
    constraints: Vec<Vec<Vec<isize>>>,
    single_base: bool,
}

impl BeliefBasesHandler {
    fn new_base(
        &mut self,
        preamble_data: Option<(usize, usize)>,
        words: &mut SplitWhitespace,
    ) -> Result<()> {
        assert_preamble_is_present(&preamble_data)?;
        let max_bases = if self.single_base {
            1
        } else {
            preamble_data.unwrap().1
        };
        if self.weights.len() == max_bases {
            return Err(anyhow!("more belief base definitions than expected"));
        }
        let w = read_belief_base_weight(words).context("while reading a belief base weight")?;
        self.weights.push(w);
        self.constraints.push(Vec::new());
        Ok(())
    }

    fn add_clause_to_last(&mut self, clause: Vec<isize>) -> Option<Vec<isize>> {
        match self.constraints.last_mut() {
            Some(cnf) => {
                cnf.push(clause);
                None
            }
            None => Some(clause),
        }
    }

    fn check_count(&self, preamble_data: Option<(usize, usize)>) -> Result<()> {
        let expected = if self.single_base {
            1
        } else {
            preamble_data.unwrap().1
        };
        if self.constraints.len() != expected {
            Err(anyhow!("less belief base definitions than expected"))
        } else {
            Ok(())
        }
    }

    fn into_cnf_vec(self, n_vars: usize) -> Vec<Weighted<CNFFormula>> {
        self.constraints
            .into_iter()
            .enumerate()
            .map(|(i, clauses)| {
                Weighted::new(
                    CNFFormula::new_from_clauses_unchecked(n_vars, clauses),
                    self.weights[i],
                )
            })
            .collect()
    }
}

impl DimacsReader {
    pub fn read<R>(&mut self, reader: R) -> Result<()>
    where
        R: Read,
    {
        let mut r = BufReader::new(reader);
        let mut buffer = String::new();
        let context = "while parsing a belief DIMACS instance";
        let line_index = Rc::new(RefCell::new(0));
        let line_index_context = || format!("while parsing line at index {}", line_index.borrow());
        loop {
            let line = r.read_line(&mut buffer)?;
            if line == 0 {
                break;
            }
            let mut words = buffer.split_whitespace();
            if let Some(first_word) = words.next() {
                match first_word {
                    "c" => {}
                    "p" => {
                        read_preamble(&mut words, &mut self.preamble_data)
                            .context("while reading the preamble")
                            .with_context(line_index_context)
                            .context(context)?;
                        self.first_formula.add_vars(self.preamble_data.unwrap().0);
                    }
                    "w" => {
                        if let WeightsType::VarWeightsMap(ref mut weights_var_map) =
                            self.weights_type
                        {
                            assert_preamble_is_present(&self.preamble_data)?;
                            read_var_weight(
                                &mut words,
                                self.preamble_data.unwrap().0,
                                weights_var_map,
                            )
                            .context("while reading a variable weight")
                            .with_context(line_index_context)
                            .context(context)?
                        } else {
                            return Err(anyhow!(r#"unexpected first word "w""#))
                                .with_context(line_index_context)
                                .context(context);
                        }
                    }
                    "t" => {
                        if let WeightsType::TopicWeights(ref mut topics) = self.weights_type {
                            assert_preamble_is_present(&self.preamble_data)?;
                            if topics.len() == self.preamble_data.unwrap().1 {
                                return Err(anyhow!("more topic definitions than expected"))
                                    .with_context(line_index_context)
                                    .context(context);
                            }
                            let weight = expect_usize(&mut words, "a topic weight as second word")?;
                            let topic = read_topic(&mut words, self.preamble_data.unwrap().0)
                                .context("while reading a topic")
                                .with_context(line_index_context)
                                .context(context)?;
                            topics.push(Weighted::new(topic, weight))
                        } else {
                            return Err(anyhow!(r#"unexpected first word "t""#))
                                .with_context(line_index_context)
                                .context(context);
                        }
                    }
                    "s" => {
                        self.belief_bases
                            .new_base(self.preamble_data, &mut words)
                            .with_context(line_index_context)
                            .context(context)?;
                    }
                    s => {
                        if let Ok(l) = str::parse::<isize>(s) {
                            assert_preamble_is_present(&self.preamble_data)?;
                            let clause = read_clause(&mut words, l, self.preamble_data.unwrap().0)
                                .context("while reading a clause")
                                .with_context(line_index_context)
                                .context(context)?;
                            if let Some(c) = self.belief_bases.add_clause_to_last(clause) {
                                self.first_formula.add_clause(c)
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
        assert_preamble_is_present(&self.preamble_data)?;
        self.belief_bases
            .check_count(self.preamble_data)
            .context(context)?;
        Ok(())
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
                if n.unsigned_abs() <= n_vars {
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
        n if n.unsigned_abs() > n_vars => {
            return Err(anyhow!(
                r#"literal {} has a variable index higher than the number of variables"#,
                n
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

fn read_topic(words: &mut SplitWhitespace, n_vars: usize) -> Result<Vec<Variable>> {
    let mut topic = Vec::new();
    loop {
        let l = expect_usize(words, "a variable index")?;
        if l > n_vars {
            return Err(anyhow!(
                "variable index {} is higher than the number of variables",
                l
            ));
        }
        if l == 0 {
            break;
        }
        topic.push(l);
    }
    expect_eol(words, "something after 0")?;
    Ok(topic)
}

fn read_belief_base_weight(words: &mut SplitWhitespace) -> Result<usize> {
    let weight = expect_usize(words, "a weight as second word")?;
    expect_eol(words, "a third word")?;
    Ok(weight)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CNFDimacsWriter;
    use std::io::BufWriter;

    #[test]
    fn test_merging_empty_instance() {
        let content = "";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_unknown_first_word() {
        let content = "a cnf 0 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_error_cnf() {
        let content = "p dnf 0 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_error_n_vars() {
        let content = "p cnf a 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_error_n_belief_bases() {
        let content = "p cnf 0 a\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_len_is_1() {
        let content = "p\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_len_is_2() {
        let content = "p cnf\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_len_is_3() {
        let content = "p cnf 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_len_is_5() {
        let content = "p cnf 0 0 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_preamble_twice() {
        let content = "p cnf 0 0\np cnf 0 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_no_preamble() {
        let content = "w 1 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_not_a_var() {
        let content = "p cnf 1 0\nw a 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_var_index_too_high() {
        let content = "p cnf 1 0\nw 2 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_not_a_weight() {
        let content = "p cnf 1 0\nw 1 a\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_len_is_1() {
        let content = "p cnf 1 0\nw\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_len_is_2() {
        let content = "p cnf 1 0\nw 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_len_is_4() {
        let content = "p cnf 1 0\nw 1 1 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_weight_multiple_definition() {
        let content = "p cnf 1 0\nw 1 1\nw 1 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_integrity_clause_not_a_lit() {
        let content = "p cnf 1 0\na 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_integrity_clause_first_var_index_too_high() {
        let content = "p cnf 1 0\n2 1 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_integrity_clause_second_var_index_too_high() {
        let content = "p cnf 1 0\n1 2 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_integrity_clause_missing_zero() {
        let content = "p cnf 1 0\n1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_integrity_clause_content_after_0() {
        let content = "p cnf 1 0\n1 0 1 0\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_too_much_belief_base_weights() {
        let content = "p cnf 1 1\ns 1\ns 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_belief_base_weight_in_not_a_weight() {
        let content = "p cnf 1 1\ns a\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_belief_base_weight_len_is_1() {
        let content = "p cnf 1 1\ns\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_belief_base_weight_len_is_3() {
        let content = "p cnf 1 1\ns 1 1\n";
        let reader = MergingDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_merging_belief_base_some_are_undef() {
        let content = "p cnf 1 1\n";
        let reader = MergingDimacsReader;
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
    fn test_merging_ok() {
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
        let reader = MergingDimacsReader;
        let problem = reader.read(content.as_bytes()).unwrap();
        assert_eq!(3, problem.n_vars());
        assert_eq!(
            vec![
                Weighted::new(1, 0),
                Weighted::new(2, 1),
                Weighted::new(3, 2)
            ],
            problem
                .var_weights()
                .iter()
                .collect::<Vec<Weighted<Variable>>>()
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

    #[test]
    fn test_revision_empty_instance() {
        let content = "";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_unknown_first_word() {
        let content = "a cnf 0 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_error_cnf() {
        let content = "p dnf 0 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_error_n_vars() {
        let content = "p cnf a 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_error_n_belief_bases() {
        let content = "p cnf 0 a\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_len_is_1() {
        let content = "p\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_len_is_2() {
        let content = "p cnf\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_len_is_3() {
        let content = "p cnf 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_len_is_5() {
        let content = "p cnf 0 0 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_preamble_twice() {
        let content = "p cnf 0 0\np cnf 0 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_no_preamble() {
        let content = "w 1 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_not_a_var() {
        let content = "p cnf 1 0\nw a 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_var_index_too_high() {
        let content = "p cnf 1 0\nw 2 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_not_a_weight() {
        let content = "p cnf 1 0\nw 1 a\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_len_is_1() {
        let content = "p cnf 1 0\nw\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_len_is_2() {
        let content = "p cnf 1 0\nw 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_len_is_4() {
        let content = "p cnf 1 0\nw 1 1 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_weight_multiple_definition() {
        let content = "p cnf 1 0\nw 1 1\nw 1 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_integrity_clause_not_a_lit() {
        let content = "p cnf 1 0\na 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_integrity_clause_first_var_index_too_high() {
        let content = "p cnf 1 0\n2 1 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_integrity_clause_second_var_index_too_high() {
        let content = "p cnf 1 0\n1 2 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_integrity_clause_missing_zero() {
        let content = "p cnf 1 0\n1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_integrity_clause_content_after_0() {
        let content = "p cnf 1 0\n1 0 1 0\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_too_much_belief_base_weights() {
        let content = "p cnf 1 1\ns 1\ns 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_belief_base_weight_in_not_a_weight() {
        let content = "p cnf 1 1\ns a\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_belief_base_weight_len_is_1() {
        let content = "p cnf 1 1\ns\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_belief_base_weight_len_is_3() {
        let content = "p cnf 1 1\ns 1 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_belief_base_some_are_undef() {
        let content = "p cnf 1 1\n";
        let reader = RevisionDimacsReader;
        assert!(reader.read(content.as_bytes()).is_err());
    }

    #[test]
    fn test_revision_ok() {
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
        let reader = RevisionDimacsReader;
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
            problem.initial_base(),
        );
    }
}
