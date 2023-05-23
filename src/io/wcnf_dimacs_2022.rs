use crate::{CNFFormula, Clause, Weighted};
use anyhow::{Context, Result};
use std::io::Write;

/// A structure used to write a DIMACS formatted WCNF formula using the format used since the MaxSAT Evaluation 2022.
#[derive(Default)]
pub struct WCNFDimacs2022Writer;

impl WCNFDimacs2022Writer {
    pub fn write(
        &self,
        writer: &mut dyn Write,
        hard_constraints: &CNFFormula,
        weighted_clauses: &[Weighted<Clause>],
    ) -> Result<()> {
        let context = "while writing a WCNF formula";
        hard_constraints
            .iter_clauses()
            .try_for_each(|cl| {
                write!(writer, "h ")?;
                cl.iter().try_for_each(|l| write!(writer, "{} ", l))?;
                writeln!(writer, "0")
            })
            .context(context)?;
        weighted_clauses
            .iter()
            .try_for_each(|wcl| {
                write!(writer, "{} ", wcl.weight())?;
                wcl.thing()
                    .iter()
                    .try_for_each(|l| write!(writer, "{} ", l))?;
                writeln!(writer, "0")
            })
            .context(context)?;
        Ok(())
    }
}
