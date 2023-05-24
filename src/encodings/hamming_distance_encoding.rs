use super::WeightedParallelCounter;
use crate::{
    core::VarWeights, CNFFormula, DiscrepancyEncoding, DistanceEncoding, ToCNFFormula, Variable,
};
use std::ops::Range;

pub struct HammingDistanceEncoding<'a> {
    discrepancy_encoding: &'a DiscrepancyEncoding<'a>,
    new_clauses: CNFFormula,
    objectives_distance_vars: Vec<Range<Variable>>,
}

impl<'a> HammingDistanceEncoding<'a> {
    pub fn new(
        discrepancy_encoding: &'a DiscrepancyEncoding<'a>,
        var_weights: &'a VarWeights,
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
    var_weights: &VarWeights,
) -> (CNFFormula, Vec<Range<Variable>>) {
    let mut cnf = CNFFormula::default();
    cnf.add_vars(discrepancy_encoding.n_vars());
    let weights = var_weights.iter().map(|w| w.weight()).collect::<Vec<_>>();
    let distance_vars = discrepancy_encoding
        .discrepancy_var_ranges()
        .map(|r| {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CNFDimacsReader, CNFDimacsWriter, DiscrepancyEncoding, Weighted};
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
        let dominated_refs = dominated.iter().collect::<Vec<&CNFFormula>>();
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &dominated_refs);
        let mut var_weights = VarWeights::new(2);
        var_weights.add(Weighted::new(1, 1));
        var_weights.add(Weighted::new(2, 2));
        let distance_encoding = HammingDistanceEncoding::new(&discrepancy_encoding, &var_weights);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(20, distance_encoding.n_vars());
        CNFDimacsWriter::default()
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
        let prevalent = CNFDimacsReader::default().read(dimacs.as_bytes()).unwrap();
        let discrepancy_encoding = DiscrepancyEncoding::new(&prevalent, &[]);
        let var_weights = VarWeights::new(2);
        let distance_encoding = HammingDistanceEncoding::new(&discrepancy_encoding, &var_weights);
        let mut writer = BufWriter::new(Vec::new());
        assert_eq!(2, distance_encoding.n_vars());
        CNFDimacsWriter::default()
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
        let distance_encoding = HammingDistanceEncoding::new(&discrepancy_encoding, &var_weights);
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
        let distance_encoding = HammingDistanceEncoding::new(&discrepancy_encoding, &var_weights);
        let distance_vars = distance_encoding.distance_vars().to_vec();
        assert_eq!(2, distance_vars.len());
        assert_eq!(3, distance_vars[0].len());
        assert_eq!(3, distance_vars[1].len());
    }
}