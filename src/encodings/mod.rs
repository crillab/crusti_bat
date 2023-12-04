mod discrepancy_encoding;
pub use discrepancy_encoding::DiscrepancyEncoding;

mod drastic_distance_encoding;
pub use drastic_distance_encoding::DrasticDistanceEncoding;

mod hamming_distance_encoding;
pub use hamming_distance_encoding::HammingDistanceEncoding;

mod leximax_aggregator_encoding;
pub use leximax_aggregator_encoding::LexiAggregatorEncoding;

mod sum_aggregator_encoding;
pub use sum_aggregator_encoding::SumAggregatorEncoding;

mod weighted_parallel_counter;
pub use weighted_parallel_counter::WeightedParallelCounter;

use crate::{core::Variable, CNFFormula, ToCNFFormula};
use anyhow::Result;
use std::ops::Range;

pub trait DistanceEncoding: ToCNFFormula {
    /// Returns the variables encoding the distances.
    ///
    /// A range of variables is dedicated to each objective function, in the order the objectives were provided.
    /// Each range defines a list of variables that encodes a binary decomposition of the objective function value.
    /// The first variable of the range is the least significant bit, the last is the most significant one.
    fn distance_vars(&self) -> &[Range<Variable>];
}

pub trait AggregatorEncoding<T>: ToCNFFormula {
    /// Returns the encoding which distances are aggregated.
    fn distance_encoding(&self) -> &dyn DistanceEncoding;

    /// Computes the optimal value for the aggregation.
    fn compute_optimum(&mut self) -> Result<T>;

    /// Enforces the aggregation has the provided value.
    fn enforce_value(&mut self, value: T) -> CNFFormula;
}
