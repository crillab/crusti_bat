use crate::{CNFFormula, Variable, Weighted};

pub struct MergingProblem {
    n_vars: usize,
    var_weights: Vec<Weighted<Variable>>,
    integrity_constraint: CNFFormula,
    belief_bases: Vec<Weighted<CNFFormula>>,
}

impl MergingProblem {
    pub fn new(
        n_vars: usize,
        var_weights: Vec<Weighted<Variable>>,
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

    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    pub fn var_weights(&self) -> &[Weighted<Variable>] {
        &self.var_weights
    }

    pub fn integrity_constraint(&self) -> &CNFFormula {
        &self.integrity_constraint
    }

    pub fn belief_bases(&self) -> &[Weighted<CNFFormula>] {
        &self.belief_bases
    }
}