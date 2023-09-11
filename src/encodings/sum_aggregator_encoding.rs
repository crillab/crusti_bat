use super::{DistanceEncoding, MaxSatEncoding};
use crate::{encodings::WeightedParallelCounter, CNFFormula, Clause, ToCNFFormula, Weighted};
use std::ops::Range;

pub struct SumAggregatorEncoding<'a> {
    distance_encoding: &'a dyn DistanceEncoding,
    distance_weights: &'a [usize],
}

impl<'a> SumAggregatorEncoding<'a> {
    pub fn new(distance_encoding: &'a dyn DistanceEncoding, distance_weights: &'a [usize]) -> Self {
        SumAggregatorEncoding {
            distance_encoding,
            distance_weights,
        }
    }

    pub fn enforce_value(self, mut value: usize) -> (CNFFormula, Range<usize>) {
        let mut cnf = self.to_cnf_formula();
        let aggregation_value_vars = WeightedParallelCounter::encode(
            self.distance_encoding.distance_vars(),
            self.distance_weights,
            &mut cnf,
        );
        aggregation_value_vars.clone().into_iter().for_each(|v| {
            if value & 1 == 1 {
                cnf.add_clause(vec![v as isize]);
            } else {
                cnf.add_clause(vec![-(v as isize)]);
            }
            value >>= 1;
        });
        (cnf, aggregation_value_vars)
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

impl MaxSatEncoding for SumAggregatorEncoding<'_> {
    fn soft_clauses(&self) -> Vec<Weighted<Clause>> {
        self.distance_encoding
            .distance_vars()
            .iter()
            .flat_map(|r| {
                r.clone()
                    .enumerate()
                    .map(|(i, v)| Weighted::new(vec![-(v as isize)], 1 << i))
            })
            .collect()
    }
}
