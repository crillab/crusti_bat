use anyhow::{Context, Result};
use std::io::{Read, Write};
use varisat_dimacs::DimacsParser;

pub type Variable = usize;

pub type Literal = isize;

pub type Clause = Vec<Literal>;

#[derive(Clone)]
pub struct CNFFormula {
    n_vars: usize,
    clauses: Vec<Clause>,
}

impl CNFFormula {
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
        if clause.iter().any(|l| l.abs() > self.n_vars as isize) {
            panic!("variable index is higher than n_vars");
        }
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

    /// Reads a DIMACS formatted CNF formula.
    ///
    /// The preamble must be exact in terms of number of variables and constraints.
    /// In case there is an issue in one of these values, an error is returned.
    pub fn from_dimacs<R>(reader: R) -> Result<Self>
    where
        R: Read,
    {
        let formula = DimacsParser::parse(reader).context("while parsing a CNF formula")?;
        let n_vars = formula.var_count();
        let clauses = formula
            .iter()
            .map(|lits| lits.iter().map(|l| l.to_dimacs()).collect())
            .collect();
        Ok(Self { n_vars, clauses })
    }

    /// Writes the CNF formula using the DIMACS format.
    pub fn to_dimacs(&self, writer: &mut dyn Write) -> Result<()> {
        let context = "while writing a CNF formula";
        writeln!(writer, "p cnf {} {}", self.n_vars, self.clauses.len()).context(context)?;
        self.clauses.iter().try_for_each(|cl| {
            cl.iter().try_for_each(|l| write!(writer, "{} ", l))?;
            writeln!(writer, "0")
        })?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufWriter;

    #[test]
    fn test_read_dimacs() {
        let dimacs = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
        let cnf = CNFFormula::from_dimacs(dimacs.as_bytes()).unwrap();
        assert_eq!(2, cnf.n_vars());
        assert_eq!(2, cnf.n_clauses());
        let mut writer = BufWriter::new(Vec::new());
        cnf.to_dimacs(&mut writer).unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_read_dimacs_empty() {
        let dimacs = "p cnf 0 0\n";
        let cnf = CNFFormula::from_dimacs(dimacs.as_bytes()).unwrap();
        assert_eq!(0, cnf.n_vars());
        assert_eq!(0, cnf.n_clauses());
        let mut writer = BufWriter::new(Vec::new());
        cnf.to_dimacs(&mut writer).unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_read_dimacs_no_clauses() {
        let dimacs = "p cnf 2 0\n";
        let cnf = CNFFormula::from_dimacs(dimacs.as_bytes()).unwrap();
        assert_eq!(2, cnf.n_vars());
        assert_eq!(0, cnf.n_clauses());
        let mut writer = BufWriter::new(Vec::new());
        cnf.to_dimacs(&mut writer).unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_read_dimacs_unknown_variable() {
        let dimacs = "p cnf 1 1\n1 2 0\n";
        assert!(CNFFormula::from_dimacs(dimacs.as_bytes()).is_err());
    }

    #[test]
    fn test_read_dimacs_not_enough_clauses() {
        let dimacs = "p cnf 1 2\n1 2 0\n";
        assert!(CNFFormula::from_dimacs(dimacs.as_bytes()).is_err());
    }

    #[test]
    fn test_read_dimacs_too_much_clauses() {
        let dimacs = "p cnf 1 1\n1 2 0\n1 2 0\n";
        assert!(CNFFormula::from_dimacs(dimacs.as_bytes()).is_err());
    }

    #[test]
    fn test_read_dimacs_not_a_lit() {
        let dimacs = "p cnf 1 1\na 2 0\n";
        assert!(CNFFormula::from_dimacs(dimacs.as_bytes()).is_err());
    }

    #[test]
    fn test_merge_into() {
        let mut cnf0 = CNFFormula::from_dimacs("p cnf 2 1\n-1 -2 0".as_bytes()).unwrap();
        let cnf1 = CNFFormula::from_dimacs("p cnf 2 1\n1 2 0".as_bytes()).unwrap();
        cnf1.merge_into(&mut cnf0);
        let mut writer = BufWriter::new(Vec::new());
        cnf0.to_dimacs(&mut writer).unwrap();
        assert_eq!(
            "p cnf 2 2\n-1 -2 0\n1 2 0\n",
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_add_offset() {
        let dimacs = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
        let mut cnf = CNFFormula::from_dimacs(dimacs.as_bytes()).unwrap();
        cnf.add_offset(3);
        let mut writer = BufWriter::new(Vec::new());
        cnf.to_dimacs(&mut writer).unwrap();
        assert_eq!(
            "p cnf 5 2\n-4 -5 0\n4 5 0\n",
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }
}
