mod core;
pub use crate::core::CNFFormula;
pub use crate::core::Clause;
pub use crate::core::ExternalMaxSatSolver;
pub use crate::core::Literal;
pub use crate::core::MaxSatSolver;
pub use crate::core::MergingProblem;
pub use crate::core::ToCNFFormula;
pub use crate::core::VarWeights;
pub use crate::core::Variable;
pub use crate::core::Weighted;

mod encodings;
pub use encodings::AggregatorEncoding;
pub use encodings::DiscrepancyEncoding;
pub use encodings::DistanceEncoding;
pub use encodings::DrasticDistanceEncoding;
pub use encodings::HammingDistanceEncoding;
pub use encodings::LexiAggregatorEncoding;
pub use encodings::SumAggregatorEncoding;

mod io;
pub use io::CNFDimacsReader;
pub use io::CNFDimacsWriter;
pub use io::MergingDimacsReader;
pub use io::WCNFDimacs2022Writer;
