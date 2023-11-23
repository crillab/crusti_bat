use super::VarWeights;
use crate::{CNFFormula, Variable, Weighted};

/// A structure used to handle belief merging problems.
pub struct MergingProblem {
    n_vars: usize,
    var_weights: VarWeights,
    integrity_constraint: CNFFormula,
    belief_bases: Vec<Weighted<CNFFormula>>,
}

impl MergingProblem {
    /// Builds a new merging problem instance.
    pub fn new(
        n_vars: usize,
        var_weights: VarWeights,
        integrity_constraint: CNFFormula,
        belief_bases: Vec<Weighted<CNFFormula>>,
    ) -> Self {
        Self {
            n_vars,
            var_weights,
            integrity_constraint,
            belief_bases,
        }
    }

    /// Returns the number of variables involved in the problem.
    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    /// Returns the weights associated with the variables, using a dedicated structure.
    pub fn var_weights(&self) -> &VarWeights {
        &self.var_weights
    }

    /// Returns the integrity constraint of the problem.
    pub fn integrity_constraint(&self) -> &CNFFormula {
        &self.integrity_constraint
    }

    /// Returns the (weighted) bases to merge.
    pub fn belief_bases(&self) -> &[Weighted<CNFFormula>] {
        &self.belief_bases
    }
}

/// A structure used to handle belief revision problems.
pub struct RevisionProblem {
    n_vars: usize,
    revision_formula: CNFFormula,
    initial_base: CNFFormula,
    topics: Vec<Weighted<Vec<Variable>>>,
}

impl RevisionProblem {
    /// Builds a new revision problem instance.
    pub fn new(
        n_vars: usize,
        revision_formula: CNFFormula,
        initial_base: CNFFormula,
        topics: Vec<Weighted<Vec<Variable>>>,
    ) -> Self {
        Self {
            n_vars,
            initial_base,
            revision_formula,
            topics,
        }
    }

    /// Returns the number of variables involved in the problem.
    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    /// Returns the initial base, that is intended to be revised.
    ///
    /// Be careful that number of variables of this CNF formula may be lower that the number of variables involved at the problem level.
    pub fn initial_base(&self) -> &CNFFormula {
        &self.initial_base
    }

    /// Returns the formula used to revised the initial one.
    ///
    /// Be careful that number of variables of this CNF formula may be lower that the number of variables involved at the problem level.
    pub fn revision_formula(&self) -> &CNFFormula {
        &self.revision_formula
    }

    /// Returns the (weighted) topics that must be used to rank the models.
    pub fn topics(&self) -> &[Weighted<Vec<Variable>>] {
        &self.topics
    }
}
