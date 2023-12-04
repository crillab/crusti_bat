use super::DistanceEncoding;
use crate::{
    core::Clause, encodings::WeightedParallelCounter, AggregatorEncoding, CNFFormula, MaxSatSolver,
    ToCNFFormula, Weighted,
};
use anyhow::{Context, Result};

pub struct SumAggregatorEncoding<'a> {
    maxsat_solver: Box<dyn MaxSatSolver>,
    distance_encoding: &'a dyn DistanceEncoding,
    distance_weights: &'a [usize],
}

impl<'a> SumAggregatorEncoding<'a> {
    pub fn new(
        distance_encoding: &'a dyn DistanceEncoding,
        distance_weights: &'a [usize],
        maxsat_solver: Box<dyn MaxSatSolver>,
    ) -> Self {
        SumAggregatorEncoding {
            maxsat_solver,
            distance_encoding,
            distance_weights,
        }
    }

    fn soft_clauses(&self) -> Vec<Weighted<Clause>> {
        self.distance_encoding
            .distance_vars()
            .iter()
            .enumerate()
            .flat_map(|(distance_index, r)| {
                r.clone().enumerate().map(move |(lit_index, v)| {
                    Weighted::new(
                        vec![-(v as isize)],
                        (1 << lit_index) * self.distance_weights[distance_index],
                    )
                })
            })
            .collect()
    }
}

impl ToCNFFormula for SumAggregatorEncoding<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        self.distance_encoding.to_cnf_formula()
    }

    fn n_vars(&self) -> usize {
        self.distance_encoding.n_vars()
    }
}

impl AggregatorEncoding<usize> for SumAggregatorEncoding<'_> {
    fn distance_encoding(&self) -> &dyn DistanceEncoding {
        self.distance_encoding
    }

    fn compute_optimum(&mut self) -> Result<usize> {
        let wcnf_hard = self.to_cnf_formula();
        let wcnf_soft = self.soft_clauses();
        self.maxsat_solver
            .solve(&wcnf_hard, &wcnf_soft)
            .context("while solving a MaxSAT problem")
            .map(|r| r.0)
    }

    fn enforce_value(&mut self, mut value: usize) -> CNFFormula {
        let mut cnf = self.to_cnf_formula();
        let aggregation_value_vars = WeightedParallelCounter::encode(
            self.distance_encoding.distance_vars(),
            self.distance_weights,
            &mut cnf,
        );
        aggregation_value_vars.clone().for_each(|v| {
            if value & 1 == 1 {
                cnf.add_clause(vec![v as isize]);
            } else {
                cnf.add_clause(vec![-(v as isize)]);
            }
            value >>= 1;
        });
        cnf
    }
}
