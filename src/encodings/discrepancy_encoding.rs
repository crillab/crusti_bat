use crate::{CNFFormula, ToCNFFormula, Variable};
use std::ops::Range;

pub struct DiscrepancyEncoding<'a> {
    prevalent: &'a CNFFormula,
    renamed_dominated: Vec<RenamedCNFFormula<'a>>,
}

impl<'a> DiscrepancyEncoding<'a> {
    pub fn new(prevalent: &'a CNFFormula, dominated: &'a [CNFFormula]) -> Self {
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

    pub fn discrepancy_var_ranges(&self) -> impl Iterator<Item = Range<usize>> + '_ {
        self.renamed_dominated.iter().map(|renamed| {
            renamed.discrepancy_var_of(1)..1 + renamed.discrepancy_var_of(self.prevalent.n_vars())
        })
    }
}

impl ToCNFFormula for DiscrepancyEncoding<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        let mut cnf_formula = self.prevalent.clone();
        self.renamed_dominated.iter().for_each(|renamed| {
            let renamed_cnf = renamed.to_cnf_formula();
            renamed_cnf.merge_into(&mut cnf_formula);
            (1..=self.prevalent.n_vars()).for_each(|i| {
                let var = i as isize;
                let renamed_var = renamed.renamed_var_of(i) as isize;
                let discrepancy_var = renamed.discrepancy_var_of(i) as isize;
                cnf_formula.add_clause(vec![discrepancy_var, -renamed_var, var]);
                cnf_formula.add_clause(vec![discrepancy_var, renamed_var, -var]);
            });
        });
        cnf_formula
    }

    fn n_vars(&self) -> usize {
        (1 + 2 * self.renamed_dominated.len()) * self.prevalent.n_vars()
    }
}

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
    use std::io::BufWriter;

    #[test]
    fn test_xor() {
        let prevalent = CNFFormula::from_dimacs("p cnf 2 2\n-1 -2 0\n1 2 0\n".as_bytes()).unwrap();
        let dominated = vec![
            CNFFormula::from_dimacs("p cnf 2 1\n1 0\n".as_bytes()).unwrap(),
            CNFFormula::from_dimacs("p cnf 2 1\n2 0\n".as_bytes()).unwrap(),
        ];
        let encoding = DiscrepancyEncoding::new(&prevalent, &dominated);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(10, encoding.n_vars());
        assert_eq!(
            vec![5..7, 9..11],
            encoding
                .discrepancy_var_ranges()
                .collect::<Vec<Range<usize>>>()
        );
        encoding.to_cnf_formula().to_dimacs(&mut writer).unwrap();
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
}
