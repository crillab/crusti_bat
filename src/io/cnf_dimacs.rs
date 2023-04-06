use crate::CNFFormula;
use anyhow::{Context, Result};
use std::io::{Read, Write};
use varisat_dimacs::DimacsParser;

/// A structure used to read a DIMACS formatted CNF formula.
///
/// The preamble must be exact in terms of number of variables and constraints.
/// In case there is an issue in one of these values, an error is returned.
#[derive(Default)]
pub struct CNFDimacsReader;

impl CNFDimacsReader {
    pub fn read<R>(&self, reader: R) -> Result<CNFFormula>
    where
        R: Read,
    {
        let formula = DimacsParser::parse(reader).context("while parsing a CNF formula")?;
        let n_vars = formula.var_count();
        let clauses = formula
            .iter()
            .map(|lits| lits.iter().map(|l| l.to_dimacs()).collect())
            .collect();
        Ok(CNFFormula::new_from_clauses_unchecked(n_vars, clauses))
    }
}

/// A structure that is used to write a CNF formula using the DIMACS format.
#[derive(Default)]
pub struct CNFDimacsWriter;

impl CNFDimacsWriter {
    pub fn write(&self, writer: &mut dyn Write, cnf_formula: &CNFFormula) -> Result<()> {
        let context = "while writing a CNF formula";
        writeln!(
            writer,
            "p cnf {} {}",
            cnf_formula.n_vars(),
            cnf_formula.n_clauses()
        )
        .context(context)?;
        cnf_formula.iter_clauses().try_for_each(|cl| {
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
        let cnf = CNFDimacsReader::default().read(dimacs.as_bytes()).unwrap();
        assert_eq!(2, cnf.n_vars());
        assert_eq!(2, cnf.n_clauses());
        let mut writer = BufWriter::new(Vec::new());
        CNFDimacsWriter::default().write(&mut writer, &cnf).unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_read_dimacs_empty() {
        let dimacs = "p cnf 0 0\n";
        let cnf = CNFDimacsReader::default().read(dimacs.as_bytes()).unwrap();
        assert_eq!(0, cnf.n_vars());
        assert_eq!(0, cnf.n_clauses());
        let mut writer = BufWriter::new(Vec::new());
        CNFDimacsWriter::default().write(&mut writer, &cnf).unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_read_dimacs_no_clauses() {
        let dimacs = "p cnf 2 0\n";
        let cnf = CNFDimacsReader::default().read(dimacs.as_bytes()).unwrap();
        assert_eq!(2, cnf.n_vars());
        assert_eq!(0, cnf.n_clauses());
        let mut writer = BufWriter::new(Vec::new());
        CNFDimacsWriter::default().write(&mut writer, &cnf).unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_read_dimacs_unknown_variable() {
        let dimacs = "p cnf 1 1\n1 2 0\n";
        assert!(CNFDimacsReader::default().read(dimacs.as_bytes()).is_err());
    }

    #[test]
    fn test_read_dimacs_not_enough_clauses() {
        let dimacs = "p cnf 1 2\n1 2 0\n";
        assert!(CNFDimacsReader::default().read(dimacs.as_bytes()).is_err());
    }

    #[test]
    fn test_read_dimacs_too_much_clauses() {
        let dimacs = "p cnf 1 1\n1 2 0\n1 2 0\n";
        assert!(CNFDimacsReader::default().read(dimacs.as_bytes()).is_err());
    }

    #[test]
    fn test_read_dimacs_not_a_lit() {
        let dimacs = "p cnf 1 1\na 2 0\n";
        assert!(CNFDimacsReader::default().read(dimacs.as_bytes()).is_err());
    }
}
