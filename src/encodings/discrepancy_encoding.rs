use crate::{CNFFormula, Variable};

pub(crate) struct DiscrepancyEncoding<'a> {
    prevalent: &'a CNFFormula,
    renamed_dominated: Vec<RenamedCNFFormula<'a>>,
    encoding: CNFFormula,
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
        let mut encoding = prevalent.clone();
        renamed_dominated.iter().for_each(|renamed| {
            let mut cnf = renamed.cnf_formula.clone();
            cnf.add_offset(renamed.offset);
            cnf.merge_into(&mut encoding);
            (1..=prevalent.n_vars()).for_each(|i| {
                let var = i as isize;
                let renamed_var = renamed.renamed_var_of(i) as isize;
                let discrepancy_var = renamed.discrepancy_var_of(i) as isize;
                encoding.add_clause(vec![discrepancy_var, -renamed_var, var]);
                encoding.add_clause(vec![discrepancy_var, renamed_var, -var]);
            });
        });
        DiscrepancyEncoding {
            prevalent,
            renamed_dominated,
            encoding,
        }
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
