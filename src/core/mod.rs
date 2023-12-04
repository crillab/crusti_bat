mod cnf;
pub use cnf::CNFFormula;
pub(crate) use cnf::Clause;
pub(crate) use cnf::Literal;
pub use cnf::ToCNFFormula;
pub(crate) use cnf::Variable;

mod maxsat_solver;
pub use maxsat_solver::ExternalMaxSatSolver;
pub use maxsat_solver::MaxSatSolver;

mod problems;
pub use problems::MergingProblem;
pub use problems::RevisionProblem;

mod weighted;
pub use weighted::VarWeights;
pub use weighted::Weighted;
