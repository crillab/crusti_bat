mod core;
pub use crate::core::CNFFormula;
pub use crate::core::Clause;
pub use crate::core::Literal;
pub use crate::core::ToCNFFormula;
pub use crate::core::Variable;
pub use crate::core::Weighted;

mod encodings;
pub use encodings::DiscrepancyEncoding;
pub use encodings::DrasticDistanceEncoding;
