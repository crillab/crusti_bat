use crate::{CNFFormula, ToCNFFormula, Variable, Weighted};
use std::ops::Range;

pub struct DrasticDistanceEncoding<'a> {
    inner_cnf: &'a dyn ToCNFFormula,
    objectives: Vec<Vec<Weighted<Variable>>>,
    objectives_weights: Vec<Vec<usize>>,
    objectives_distance_vars: Vec<Range<usize>>,
    objectives_rank_vars: Vec<Range<usize>>,
}

impl<'a> DrasticDistanceEncoding<'a> {
    pub fn new(inner_cnf: &'a dyn ToCNFFormula, objectives: Vec<Vec<Weighted<Variable>>>) -> Self {
        let weights = objectives
            .iter()
            .map(|o| {
                let mut weights = o.iter().map(|w| w.weight()).collect::<Vec<usize>>();
                weights.sort_unstable();
                weights.dedup();
                weights
            })
            .collect::<Vec<Vec<usize>>>();
        let mut offset = 1;
        let distance_vars = weights
            .iter()
            .map(|w| {
                let n_distance_vars = f64::log2((1 + *w.last().unwrap()) as f64).ceil() as usize;
                let range =
                    offset + inner_cnf.n_vars()..offset + inner_cnf.n_vars() + n_distance_vars;
                offset += range.len();
                range
            })
            .collect::<Vec<Range<usize>>>();
        let rank_vars = weights
            .iter()
            .map(|w| {
                let range = offset + inner_cnf.n_vars()..offset + inner_cnf.n_vars() + w.len();
                offset += range.len();
                range
            })
            .collect();
        DrasticDistanceEncoding {
            inner_cnf,
            objectives,
            objectives_weights: weights,
            objectives_distance_vars: distance_vars,
            objectives_rank_vars: rank_vars,
        }
    }

    fn encode_ranks_cascades(&self, objective_index: usize, cnf_formula: &mut CNFFormula) {
        (1..self.objectives_weights[objective_index].len()).for_each(|j| {
            cnf_formula.add_clause_unchecked(vec![
                -self.rank_lit(objective_index, j),
                self.rank_lit(objective_index, j - 1),
            ]);
        });
    }

    fn encode_objective_lits_to_ranks(&self, objective_index: usize, cnf_formula: &mut CNFFormula) {
        self.objectives[objective_index]
            .iter()
            .for_each(|weighted_var| {
                cnf_formula.add_clause_unchecked(vec![
                    -(*weighted_var.thing() as isize),
                    self.rank_lit(
                        objective_index,
                        self.objectives_weights[objective_index]
                            .iter()
                            .position(|w| *w == weighted_var.weight())
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
        let weights = &self.objectives_weights[objective_index];
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
            vec![(rank_vars.end as isize) - 1],
            *weights.last().unwrap(),
            distance_vars,
        );
    }
}

impl ToCNFFormula for DrasticDistanceEncoding<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        let mut cnf_formula = self.inner_cnf.to_cnf_formula();
        (0..self.objectives.len()).for_each(|objective_index| {
            cnf_formula.add_vars(self.n_vars() - cnf_formula.n_vars());
            self.encode_ranks_cascades(objective_index, &mut cnf_formula);
            self.encode_objective_lits_to_ranks(objective_index, &mut cnf_formula);
            self.encode_ranks_to_values(objective_index, &mut cnf_formula);
        });
        cnf_formula
    }

    fn n_vars(&self) -> usize {
        self.inner_cnf.n_vars()
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
    use crate::{CNFDimacsReader, CNFDimacsWriter, DiscrepancyEncoding};
    use std::io::BufWriter;

    #[test]
    fn test_xor() {
        let prevalent = CNFDimacsReader::default()
            .read("p cnf 2 2\n-1 -2 0\n1 2 0\n".as_bytes())
            .unwrap();
        let dominated = vec![
            CNFDimacsReader::default()
                .read("p cnf 2 1\n1 0\n".as_bytes())
                .unwrap(),
            CNFDimacsReader::default()
                .read("p cnf 2 1\n2 0\n".as_bytes())
                .unwrap(),
        ];
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &dominated);
        let objectives = discrepancy_encoding
            .discrepancy_var_ranges()
            .map(|r| {
                r.enumerate()
                    .map(|(i, v)| Weighted::new(v, 1 + i))
                    .collect()
            })
            .collect();
        let drastic_distance_encoding =
            DrasticDistanceEncoding::new(&discrepancy_encoding, objectives);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(18, drastic_distance_encoding.n_vars());
        CNFDimacsWriter::default()
            .write(&mut writer, &drastic_distance_encoding.to_cnf_formula())
            .unwrap();
        let expected = r#"p cnf 18 26
-1 -2 0
1 2 0
3 0
5 -3 1 0
5 3 -1 0
6 -4 2 0
6 4 -2 0
8 0
9 -7 1 0
9 7 -1 0
10 -8 2 0
10 8 -2 0
-16 15 0
-5 15 0
-6 16 0
-15 16 11 0
-15 16 -12 0
-16 -11 0
-16 12 0
-18 17 0
-9 17 0
-10 18 0
-17 18 13 0
-17 18 -14 0
-18 -13 0
-18 14 0
"#;
        assert_eq!(
            expected,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        )
    }

    #[test]
    fn test_no_objectives() {
        let dimacs = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
        let prevalent = CNFDimacsReader::default().read(dimacs.as_bytes()).unwrap();
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &[]);
        let drastic_distance_encoding = DrasticDistanceEncoding::new(&discrepancy_encoding, vec![]);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(2, drastic_distance_encoding.n_vars());
        CNFDimacsWriter::default()
            .write(&mut writer, &drastic_distance_encoding.to_cnf_formula())
            .unwrap();
        assert_eq!(
            dimacs,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        )
    }
}
