use crate::{
    core::{ToCNFFormula, Variable},
    CNFFormula,
};
use itertools::Itertools;
use std::ops::Range;

/// Given a prevalent knowledge (integrity constraints, a new certain piece of information) and a set of beliefs,
/// this structure allow the construction of a CNF formula that can be used to check if a conjunction of the prevalent knowledge and a subset of the beliefs is coherent.
///
/// The encoding proceeds by renaming the variables in each belief and to declare discrepancy variables, that must be set to true if the renamed variable in the belief cannot be set as equivalent to the original variable.
/// With this encoding, minimizing the amount of discrepancy variables set to true increases the amount of coherent knowledge.
pub struct DiscrepancyEncoding<'a> {
    prevalent: &'a CNFFormula,
    renamed_dominated: Vec<RenamedCNFFormula<'a>>,
}

impl<'a> DiscrepancyEncoding<'a> {
    /// Builds a discrepancy encoding from a prevalent knowledge and a set a beliefs.
    ///
    /// Each belief is associated with a new fresh set of discrepancy variables.
    pub fn new(prevalent: &'a CNFFormula, dominated: &'a [&CNFFormula]) -> Self {
        let renamed_dominated: Vec<RenamedCNFFormula<'a>> = dominated
            .iter()
            .enumerate()
            .map(|(i, d)| RenamedCNFFormula {
                cnf_formula: d,
                offset: (2 * i + 1) * prevalent.n_vars(),
            })
            .collect();
        DiscrepancyEncoding {
            prevalent,
            renamed_dominated,
        }
    }

    /// Builds a discrepancy encoding from a prevalent knowledge and a single belief base.
    ///
    /// A set of discrepancy variables is constructed for the belief base.
    /// This structure stores this set `n` times, just like `n` equivalent belief bases were involved.
    pub fn new_repeated(prevalent: &'a CNFFormula, dominated: &'a CNFFormula, n: usize) -> Self {
        let renamed_dominated = std::iter::repeat(RenamedCNFFormula {
            cnf_formula: dominated,
            offset: prevalent.n_vars(),
        })
        .take(n)
        .collect::<Vec<_>>();
        DiscrepancyEncoding {
            prevalent,
            renamed_dominated,
        }
    }

    /// Returns an iterator to the set of discrepancy variables stored in this structure.
    pub fn discrepancy_var_ranges(&self) -> impl Iterator<Item = Range<usize>> + '_ {
        self.renamed_dominated.iter().map(|renamed| {
            renamed.discrepancy_var_of(1)..1 + renamed.discrepancy_var_of(self.prevalent.n_vars())
        })
    }
}

impl ToCNFFormula for DiscrepancyEncoding<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        let mut cnf_formula = self.prevalent.clone();
        self.renamed_dominated
            .iter()
            .dedup_by(|c0, c1| {
                std::ptr::eq(c0.cnf_formula, c1.cnf_formula) && c0.offset == c1.offset
            })
            .for_each(|renamed| {
                let renamed_cnf = renamed.to_cnf_formula();
                renamed_cnf.merge_into(&mut cnf_formula);
                (1..=self.prevalent.n_vars()).for_each(|i| {
                    let var = i as isize;
                    let renamed_var = renamed.renamed_var_of(i) as isize;
                    let discrepancy_var = renamed.discrepancy_var_of(i) as isize;
                    cnf_formula.add_clause_unchecked(vec![discrepancy_var, -renamed_var, var]);
                    cnf_formula.add_clause_unchecked(vec![discrepancy_var, renamed_var, -var]);
                });
            });
        cnf_formula
    }

    fn n_vars(&self) -> usize {
        (1 + 2 * self
            .renamed_dominated
            .iter()
            .dedup_by(|c0, c1| {
                std::ptr::eq(c0.cnf_formula, c1.cnf_formula) && c0.offset == c1.offset
            })
            .count())
            * self.prevalent.n_vars()
    }
}

#[derive(Clone)]
pub(crate) struct RenamedCNFFormula<'a> {
    cnf_formula: &'a CNFFormula,
    offset: usize,
}

impl RenamedCNFFormula<'_> {
    fn renamed_var_of(&self, v: Variable) -> Variable {
        v + self.offset
    }

    fn discrepancy_var_of(&self, v: Variable) -> Variable {
        v + self.offset + self.cnf_formula.n_vars()
    }
}

impl ToCNFFormula for RenamedCNFFormula<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        let mut renamed_cnf = self.cnf_formula.clone();
        renamed_cnf.add_offset(self.offset);
        renamed_cnf.add_vars(self.cnf_formula.n_vars());
        renamed_cnf
    }

    fn n_vars(&self) -> usize {
        self.offset + 3 * self.cnf_formula.n_vars()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{io::CNFDimacsReader, CNFDimacsWriter};
    use std::io::BufWriter;

    #[test]
    fn test_xor() {
        let prevalent = CNFDimacsReader
            .read("p cnf 2 2\n-1 -2 0\n1 2 0\n".as_bytes())
            .unwrap();
        let dominated = vec![
            CNFDimacsReader.read("p cnf 2 1\n1 0\n".as_bytes()).unwrap(),
            CNFDimacsReader.read("p cnf 2 1\n2 0\n".as_bytes()).unwrap(),
        ];
        let dominated_refs = dominated.iter().collect::<Vec<&CNFFormula>>();
        let encoding = DiscrepancyEncoding::new(&prevalent, &dominated_refs);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(10, encoding.n_vars());
        assert_eq!(
            vec![5..7, 9..11],
            encoding
                .discrepancy_var_ranges()
                .collect::<Vec<Range<usize>>>()
        );
        CNFDimacsWriter
            .write(&mut writer, &encoding.to_cnf_formula())
            .unwrap();
        let expected = r#"p cnf 10 12
-1 -2 0
1 2 0
3 0
5 -3 1 0
5 3 -1 0
6 -4 2 0
6 4 -2 0
8 0
9 -7 1 0
9 7 -1 0
10 -8 2 0
10 8 -2 0
"#;
        assert_eq!(
            expected,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        )
    }

    #[test]
    fn test_no_profile() {
        let dimacs = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
        let prevalent = CNFDimacsReader.read(dimacs.as_bytes()).unwrap();
        let encoding = DiscrepancyEncoding::new(&prevalent, &[]);
        assert_eq!(2, encoding.n_vars());
        assert_eq!(0, encoding.discrepancy_var_ranges().count());
        let mut writer = BufWriter::new(Vec::new());
        CNFDimacsWriter
            .write(&mut writer, &encoding.to_cnf_formula())
            .unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        )
    }

    #[test]
    fn test_no_clauses() {
        let prevalent = CNFFormula::new_from_clauses(2, vec![]);
        let dominated1 = CNFFormula::new_from_clauses(2, vec![vec![1]]);
        let dominated2 = CNFFormula::new_from_clauses(2, vec![vec![2]]);
        let dominated = vec![&dominated1, &dominated2];
        let encoding = DiscrepancyEncoding::new(&prevalent, &dominated);
        let discrepancy_var_ranges = encoding
            .discrepancy_var_ranges()
            .collect::<Vec<Range<Variable>>>();
        assert_eq!(2, discrepancy_var_ranges.len());
        discrepancy_var_ranges.iter().for_each(|r| {
            assert_eq!(2, r.len());
        });
    }
}
