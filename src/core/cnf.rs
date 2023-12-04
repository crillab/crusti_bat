pub(crate) type Variable = usize;

pub(crate) type Literal = isize;

pub(crate) type Clause = Vec<Literal>;

#[derive(Clone, Default)]
pub struct CNFFormula {
    n_vars: usize,
    clauses: Vec<Clause>,
}

impl CNFFormula {
    /// Returns a new CNF formula initialized with the given number of variables and the given clauses.
    ///
    /// # Panics
    ///
    /// In case the clause involves variable indexes that are higher than the provided number of variables, this function panics.
    pub fn new_from_clauses(n_vars: usize, clauses: Vec<Clause>) -> Self {
        clauses.iter().for_each(|cl| check_clause(cl, n_vars));
        Self::new_from_clauses_unchecked(n_vars, clauses)
    }

    pub(crate) fn new_from_clauses_unchecked(n_vars: usize, clauses: Vec<Clause>) -> Self {
        clauses.iter().for_each(|cl| check_clause(cl, n_vars));
        Self { n_vars, clauses }
    }

    /// Returns the number of variables associated with this CNF formula.
    ///
    /// The number of variables is typically set when the CNF formula is created, and updated by relevant functions.
    /// This number may thus be higher that the highest variable index present in the clauses.
    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    /// Returns the number of clauses contained in this CNF formula.
    pub fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Adds a clause to the CNF formula.
    ///
    /// # Panics
    ///
    /// In case the clause involves variable indexes that are higher than the number of variables associated with this CNF formula, this function panics.
    pub fn add_clause(&mut self, clause: Clause) {
        check_clause(&clause, self.n_vars);
        self.add_clause_unchecked(clause);
    }

    pub(crate) fn add_clause_unchecked(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }

    /// Iterates over the clauses of this CNF formula.
    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> + '_ {
        self.clauses.iter()
    }

    pub(crate) fn merge_into(mut self, other: &mut CNFFormula) {
        other.n_vars = usize::max(self.n_vars, other.n_vars);
        other.clauses.append(&mut self.clauses);
    }

    pub(crate) fn add_vars(&mut self, n: usize) {
        self.n_vars += n;
    }

    pub(crate) fn add_offset(&mut self, offset: usize) {
        self.n_vars += offset;
        self.clauses.iter_mut().for_each(|cl| {
            cl.iter_mut().for_each(|l| {
                *l = if *l < 0 {
                    *l - offset as isize
                } else {
                    *l + offset as isize
                };
            })
        });
    }
}

fn check_clause(clause: &Clause, n_vars: usize) {
    if clause.iter().any(|l| l.abs() > n_vars as isize) {
        panic!("variable index is higher than n_vars");
    }
}

pub trait ToCNFFormula {
    fn to_cnf_formula(&self) -> CNFFormula;

    fn n_vars(&self) -> usize;
}

#[cfg(test)]
mod tests {
    use crate::{io::CNFDimacsReader, CNFDimacsWriter};
    use std::io::BufWriter;

    #[test]
    fn test_merge_into() {
        let mut cnf0 = CNFDimacsReader
            .read("p cnf 2 1\n-1 -2 0".as_bytes())
            .unwrap();
        let cnf1 = CNFDimacsReader.read("p cnf 2 1\n1 2 0".as_bytes()).unwrap();
        cnf1.merge_into(&mut cnf0);
        let mut writer = BufWriter::new(Vec::new());
        CNFDimacsWriter.write(&mut writer, &cnf0).unwrap();
        assert_eq!(
            "p cnf 2 2\n-1 -2 0\n1 2 0\n",
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_add_offset() {
        let dimacs = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
        let mut cnf = CNFDimacsReader.read(dimacs.as_bytes()).unwrap();
        cnf.add_offset(3);
        let mut writer = BufWriter::new(Vec::new());
        CNFDimacsWriter.write(&mut writer, &cnf).unwrap();
        assert_eq!(
            "p cnf 5 2\n-4 -5 0\n4 5 0\n",
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }
}
