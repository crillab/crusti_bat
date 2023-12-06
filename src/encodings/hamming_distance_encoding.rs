use super::WeightedParallelCounter;
use crate::{
    core::{ToCNFFormula, VarWeights, Variable},
    CNFFormula, DiscrepancyEncoding, DistanceEncoding,
};
use std::ops::Range;

/// An encoding for the hamming distance.
///
/// Given a set of discrepancy variables related to a belief problem (see [`DiscrepancyEncoding`]) and variable weights,
/// this structure encodes as a binary decomposition the sum of the weights involved in the discrepancy variables set to true.
pub struct HammingDistanceEncoding<'a> {
    discrepancy_encoding: &'a DiscrepancyEncoding<'a>,
    new_clauses: CNFFormula,
    objectives_distance_vars: Vec<Range<Variable>>,
}

impl<'a> HammingDistanceEncoding<'a> {
    /// Builds a new hamming distance encoding.
    pub fn new(
        discrepancy_encoding: &'a DiscrepancyEncoding<'a>,
        var_weights: Vec<&'a VarWeights>,
    ) -> Self {
        let (new_clauses, distance_vars) = encode_distances(discrepancy_encoding, var_weights);
        HammingDistanceEncoding {
            discrepancy_encoding,
            new_clauses,
            objectives_distance_vars: distance_vars,
        }
    }
}

fn encode_distances(
    discrepancy_encoding: &DiscrepancyEncoding,
    var_weights: Vec<&VarWeights>,
) -> (CNFFormula, Vec<Range<Variable>>) {
    let mut cnf = CNFFormula::default();
    cnf.add_vars(discrepancy_encoding.n_vars());
    let distance_vars = discrepancy_encoding
        .discrepancy_var_ranges()
        .enumerate()
        .map(|(i, r)| {
            let mut weights = vec![0; r.len()];
            var_weights[i]
                .iter()
                .for_each(|w| weights[w.thing() - 1] = w.weight());
            let range_decomposition = r.into_iter().map(|v| v..v + 1).collect::<Vec<_>>();
            WeightedParallelCounter::encode(&range_decomposition, &weights, &mut cnf)
        })
        .collect();
    (cnf, distance_vars)
}

impl ToCNFFormula for HammingDistanceEncoding<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        let mut cnf = self.discrepancy_encoding.to_cnf_formula();
        self.new_clauses.clone().merge_into(&mut cnf);
        cnf
    }

    fn n_vars(&self) -> usize {
        self.new_clauses.n_vars()
    }
}

impl DistanceEncoding for HammingDistanceEncoding<'_> {
    fn distance_vars(&self) -> &[Range<Variable>] {
        &self.objectives_distance_vars
    }

    fn auxiliary_vars(&self) -> Vec<(&'static str, Vec<Range<Variable>>)> {
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{io::CNFDimacsReader, CNFDimacsWriter, DiscrepancyEncoding, Weighted};
    use std::io::BufWriter;

    #[test]
    fn test_xor() {
        let prevalent = CNFDimacsReader
            .read("p cnf 2 2\n-1 -2 0\n1 2 0\n".as_bytes())
            .unwrap();
        let dominated = vec![
            CNFDimacsReader.read("p cnf 2 1\n1 0\n".as_bytes()).unwrap(),
            CNFDimacsReader.read("p cnf 2 1\n2 0\n".as_bytes()).unwrap(),
        ];
        let dominated_refs = dominated.iter().collect::<Vec<&CNFFormula>>();
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &dominated_refs);
        let mut var_weights = VarWeights::new(2);
        var_weights.add(Weighted::new(1, 1));
        var_weights.add(Weighted::new(2, 2));
        let var_weights_vec = vec![&var_weights, &var_weights];
        let distance_encoding =
            HammingDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(20, distance_encoding.n_vars());
        CNFDimacsWriter
            .write(&mut writer, &distance_encoding.to_cnf_formula())
            .unwrap();
        let expected = r#"p cnf 20 20
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
-5 13 0
-6 11 14 0
6 -11 14 0
-6 -11 15 0
-9 18 0
-10 16 19 0
10 -16 19 0
-10 -16 20 0
"#;
        assert_eq!(
            expected,
            String::from_utf8(writer.into_inner().unwrap()).unwrap()
        )
    }

    #[test]
    fn test_no_objectives() {
        let dimacs = "p cnf 2 2\n-1 -2 0\n1 2 0\n";
        let prevalent = CNFDimacsReader.read(dimacs.as_bytes()).unwrap();
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &[]);
        let var_weights = VarWeights::new(2);
        let var_weights_vec = vec![&var_weights, &var_weights];
        let distance_encoding =
            HammingDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(2, distance_encoding.n_vars());
        CNFDimacsWriter
            .write(&mut writer, &distance_encoding.to_cnf_formula())
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
        let distance_encoding =
            HammingDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let distance_vars = distance_encoding.distance_vars().to_vec();
        assert_eq!(2, distance_vars.len());
        distance_vars.iter().for_each(|r| assert_eq!(2, r.len()));
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
        let distance_encoding =
            HammingDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let distance_vars = distance_encoding.distance_vars().to_vec();
        assert_eq!(2, distance_vars.len());
        assert_eq!(3, distance_vars[0].len());
        assert_eq!(3, distance_vars[1].len());
    }
}
