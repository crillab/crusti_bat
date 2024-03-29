use super::DistanceEncoding;
use crate::{
    core::{ToCNFFormula, VarWeights, Variable},
    CNFFormula, DiscrepancyEncoding,
};
use std::ops::Range;

/// An encoding for the drastic distance.
///
/// Given a set of discrepancy variables related to a belief problem (see [`DiscrepancyEncoding`]) and variable weights,
/// this structure encodes as a binary decomposition the maximal weight involved in the discrepancy variables set to true.
pub struct DrasticDistanceEncoding<'a> {
    discrepancy_encoding: &'a DiscrepancyEncoding<'a>,
    var_weights: Vec<&'a VarWeights>,
    discrepancy_var_ranges: Vec<Range<Variable>>,
    objectives_distance_vars: Vec<Range<Variable>>,
    objectives_rank_vars: Vec<Range<Variable>>,
}

impl<'a> DrasticDistanceEncoding<'a> {
    /// Builds a new drastic distance encoding.
    pub fn new(
        discrepancy_encoding: &'a DiscrepancyEncoding<'a>,
        var_weights: Vec<&'a VarWeights>,
    ) -> Self {
        assert_eq!(
            discrepancy_encoding.discrepancy_var_ranges().count(),
            var_weights.len()
        );
        let n_distance_vars = var_weights
            .iter()
            .map(|vw| f64::log2((1 + vw.max_weight().unwrap_or_default()) as f64).ceil() as usize)
            .max()
            .unwrap_or_default();
        let discrepancy_var_ranges = discrepancy_encoding
            .discrepancy_var_ranges()
            .collect::<Vec<Range<Variable>>>();
        let n_objectives = discrepancy_var_ranges.len();
        let distance_vars = (0..n_objectives)
            .map(|i| {
                1 + i * n_distance_vars + discrepancy_encoding.n_vars()
                    ..1 + i * n_distance_vars + discrepancy_encoding.n_vars() + n_distance_vars
            })
            .collect::<Vec<Range<usize>>>();
        let mut next_var = 1 + n_objectives * n_distance_vars + discrepancy_encoding.n_vars();
        let rank_vars = (0..n_objectives)
            .map(|i| {
                let all_weights = var_weights_set(var_weights[i]);
                let r = next_var..next_var + all_weights.len();
                next_var += all_weights.len();
                r
            })
            .collect();
        DrasticDistanceEncoding {
            discrepancy_encoding,
            var_weights,
            discrepancy_var_ranges,
            objectives_distance_vars: distance_vars,
            objectives_rank_vars: rank_vars,
        }
    }

    fn encode_ranks_cascades(&self, objective_index: usize, cnf_formula: &mut CNFFormula) {
        (1..var_weights_set(self.var_weights[objective_index])
            .len())
            .for_each(|j| {
                cnf_formula.add_clause_unchecked(vec![
                    -self.rank_lit(objective_index, j),
                    self.rank_lit(objective_index, j - 1),
                ]);
            });
    }

    fn encode_objective_lits_to_ranks(&self, objective_index: usize, cnf_formula: &mut CNFFormula) {
        self.discrepancy_var_ranges[objective_index]
            .clone()
            .enumerate()
            .for_each(|(i, discrepancy_var)| {
                cnf_formula.add_clause_unchecked(vec![
                    -(discrepancy_var as isize),
                    self.rank_lit(
                        objective_index,
                        var_weights_set(self.var_weights[objective_index])
                            .iter()
                            .position(|w| {
                                *w == self.var_weights[objective_index][i + 1]
                                    .map(|w| w.weight())
                                    .unwrap_or_default()
                            })
                            .unwrap(),
                    ),
                ]);
            });
    }

    fn rank_lit(&self, objective_index: usize, rank: usize) -> isize {
        (self.objectives_rank_vars[objective_index].start + rank) as isize
    }

    fn encode_ranks_to_values(&self, objective_index: usize, cnf_formula: &mut CNFFormula) {
        let rank_vars = &self.objectives_rank_vars[objective_index];
        let weights = var_weights_set(self.var_weights[objective_index]);
        let distance_vars = &self.objectives_distance_vars[objective_index];
        (rank_vars.start..rank_vars.end - 1)
            .enumerate()
            .for_each(|(i, rank_var)| {
                encode_rank_value(
                    cnf_formula,
                    vec![rank_var as isize, -(rank_var as isize) - 1],
                    weights[i],
                    distance_vars,
                );
            });
        encode_rank_value(
            cnf_formula,
            vec![rank_vars.end as isize - 1],
            *weights.last().unwrap(),
            distance_vars,
        );
    }
}

impl ToCNFFormula for DrasticDistanceEncoding<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        let mut cnf_formula = self.discrepancy_encoding.to_cnf_formula();
        (0..self.objectives_rank_vars.len()).for_each(|objective_index| {
            cnf_formula.add_vars(self.n_vars() - cnf_formula.n_vars());
            self.encode_ranks_cascades(objective_index, &mut cnf_formula);
            self.encode_objective_lits_to_ranks(objective_index, &mut cnf_formula);
            self.encode_ranks_to_values(objective_index, &mut cnf_formula);
        });
        cnf_formula
    }

    fn n_vars(&self) -> usize {
        self.discrepancy_encoding.n_vars()
            + self
                .objectives_distance_vars
                .iter()
                .map(|d| d.len())
                .sum::<usize>()
            + self
                .objectives_rank_vars
                .iter()
                .map(|d| d.len())
                .sum::<usize>()
    }
}

impl DistanceEncoding for DrasticDistanceEncoding<'_> {
    fn distance_vars(&self) -> &[Range<Variable>] {
        &self.objectives_distance_vars
    }

    fn auxiliary_vars(&self) -> Vec<(&'static str, Vec<Range<Variable>>)> {
        vec![(
            "ranking (in drastic distance)",
            self.objectives_rank_vars.clone(),
        )]
    }
}

fn var_weights_set(vw: &VarWeights) -> Vec<usize> {
    let mut weights = vw.weights_sorted_dedup().iter().copied().collect::<Vec<_>>();
    if weights[0] == 0 {
        weights
    } else {
        let mut weights_with_zero = Vec::with_capacity(weights.len() + 1);
        weights_with_zero.push(0);
        weights_with_zero.append(&mut weights);
        weights_with_zero
    }
}

fn encode_rank_value(
    cnf: &mut CNFFormula,
    rank_lits: Vec<isize>,
    value: usize,
    distance_vars: &Range<usize>,
) {
    let mut bit_mask = 1;
    distance_vars.to_owned().for_each(|distance_var| {
        let lit = if value & bit_mask != 0 {
            distance_var as isize
        } else {
            -(distance_var as isize)
        };
        let clause = rank_lits
            .iter()
            .map(|l| -l)
            .chain(std::iter::once(lit))
            .collect();
        cnf.add_clause_unchecked(clause);
        bit_mask <<= 1;
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{io::CNFDimacsReader, CNFDimacsWriter, DiscrepancyEncoding, Weighted};
    use std::io::BufWriter;

    //     #[test]
    //     fn test_xor() {
    //         let prevalent = CNFDimacsReader
    //             .read("p cnf 2 2\n-1 -2 0\n1 2 0\n".as_bytes())
    //             .unwrap();
    //         let dominated = vec![
    //             CNFDimacsReader.read("p cnf 2 1\n1 0\n".as_bytes()).unwrap(),
    //             CNFDimacsReader.read("p cnf 2 1\n2 0\n".as_bytes()).unwrap(),
    //         ];
    //         let dominated_refs = dominated.iter().collect::<Vec<&CNFFormula>>();
    //         let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &dominated_refs);
    //         let mut var_weights = VarWeights::new(2);
    //         var_weights.add(Weighted::new(1, 1));
    //         var_weights.add(Weighted::new(2, 2));
    //         let var_weights_vec = vec![&var_weights, &var_weights];
    //         let drastic_distance_encoding =
    //             DrasticDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
    //         let mut writer = BufWriter::new(Vec::new());
    //         assert_eq!(18, drastic_distance_encoding.n_vars());
    //         CNFDimacsWriter
    //             .write(&mut writer, &drastic_distance_encoding.to_cnf_formula())
    //             .unwrap();
    //         let expected = r#"p cnf 18 26
    // -1 -2 0
    // 1 2 0
    // 3 0
    // 5 -3 1 0
    // 5 3 -1 0
    // 6 -4 2 0
    // 6 4 -2 0
    // 8 0
    // 9 -7 1 0
    // 9 7 -1 0
    // 10 -8 2 0
    // 10 8 -2 0
    // -16 15 0
    // -5 15 0
    // -6 16 0
    // -15 16 11 0
    // -15 16 -12 0
    // -16 -11 0
    // -16 12 0
    // -18 17 0
    // -9 17 0
    // -10 18 0
    // -17 18 13 0
    // -17 18 -14 0
    // -18 -13 0
    // -18 14 0
    // "#;
    //         assert_eq!(
    //             expected,
    //             String::from_utf8(writer.into_inner().unwrap()).unwrap()
    //         )
    //     }

    #[test]
    fn test_no_objectives() {
        let dimacs = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
        let prevalent = CNFDimacsReader.read(dimacs.as_bytes()).unwrap();
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &[]);
        let drastic_distance_encoding = DrasticDistanceEncoding::new(&discrepancy_encoding, vec![]);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(2, drastic_distance_encoding.n_vars());
        CNFDimacsWriter
            .write(&mut writer, &drastic_distance_encoding.to_cnf_formula())
            .unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        )
    }

    #[test]
    fn test_no_weights() {
        let prevalent = CNFFormula::new_from_clauses(2, vec![]);
        let dominated1 = CNFFormula::new_from_clauses(2, vec![vec![1]]);
        let dominated2 = CNFFormula::new_from_clauses(2, vec![vec![2]]);
        let dominated = vec![&dominated1, &dominated2];
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &dominated);
        let mut var_weights = VarWeights::new(2);
        var_weights.add(Weighted::new(1, 1));
        var_weights.add(Weighted::new(2, 1));
        let var_weights_vec = vec![&var_weights, &var_weights];
        let drastic_distance_encoding =
            DrasticDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let distance_vars = drastic_distance_encoding.distance_vars().to_vec();
        assert_eq!(2, distance_vars.len());
        distance_vars.iter().for_each(|r| assert_eq!(1, r.len()));
    }

    #[test]
    fn test_with_weights() {
        let prevalent = CNFFormula::new_from_clauses(2, vec![]);
        let dominated1 = CNFFormula::new_from_clauses(2, vec![vec![1]]);
        let dominated2 = CNFFormula::new_from_clauses(2, vec![vec![2]]);
        let dominated = vec![&dominated1, &dominated2];
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &dominated);
        let mut var_weights = VarWeights::new(2);
        var_weights.add(Weighted::new(1, 1));
        var_weights.add(Weighted::new(2, 2));
        let var_weights_vec = vec![&var_weights, &var_weights];
        let drastic_distance_encoding =
            DrasticDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let distance_vars = drastic_distance_encoding.distance_vars().to_vec();
        assert_eq!(2, distance_vars.len());
        assert_eq!(2, distance_vars[0].len());
        assert_eq!(2, distance_vars[1].len());
    }
}
