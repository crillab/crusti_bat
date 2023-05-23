mod discrepancy_encoding;
pub use discrepancy_encoding::DiscrepancyEncoding;

mod drastic_distance_encoding;
pub use drastic_distance_encoding::DrasticDistanceEncoding;

use crate::{ToCNFFormula, Variable};
use std::ops::Range;

pub trait DistanceEncoding: ToCNFFormula {
    /// Returns the variables encoding the distances.
    ///
    /// A range of variables is dedicated to each objective function, in the order the objectives were provided.
    /// Each range defines a list of variables that encodes a binary decomposition of the objective function value.
    /// The first variable of the range is the least significant bit, the last is the most significant one.
    fn distance_vars(&self) -> &[Range<Variable>];
}

