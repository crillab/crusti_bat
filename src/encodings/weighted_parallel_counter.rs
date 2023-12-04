use crate::{core::Variable, CNFFormula};
use std::ops::Range;

pub struct WeightedParallelCounter;

#[derive(Debug)]
struct BitShiftRange(Range<Variable>, usize);

impl BitShiftRange {
    /// Returns the length of the range (does not consider the shifting).
    fn range_len(&self) -> usize {
        self.0.end - self.0.start
    }

    /// Returns the shifting value.
    fn shift(&self) -> usize {
        self.1
    }

    /// Decreases the shifting value by the provided amount.
    /// Panics if the provided value is higher than the current shifting value.
    fn decrease_shift(&mut self, dec: usize) {
        if dec > self.1 {
            panic!()
        }
        self.1 -= dec
    }

    /// Increases the shifting value by the provided amount.
    fn increase_shift(&mut self, inc: usize) {
        self.1 += inc
    }

    /// Returns the total number of bits: the range length + the shifting value.
    fn n_bits(&self) -> usize {
        self.range_len() + self.1
    }

    /// Returns the variable from the range that correspond to the provided bit index.
    /// If such index does not refer to an existing variable (index is lower to the shifting or higher than the total number of bits), `None` is returned.
    fn bit(&self, bit_index: usize) -> Option<Variable> {
        if bit_index >= self.1 && bit_index < self.n_bits() {
            Some(self.0.start + bit_index - self.1)
        } else {
            None
        }
    }

    /// Translates this shifted range into a regular one.
    /// Panics if the shifted index is not null.
    fn into_range(self) -> Range<Variable> {
        assert_eq!(0, self.1);
        self.0
    }
}

impl WeightedParallelCounter {
    pub fn encode(
        sum_operands: &[Range<Variable>],
        operand_weights: &[usize],
        cnf: &mut CNFFormula,
    ) -> Range<Variable> {
        let mut bitshift_sum = input_as_bitshift_sum(sum_operands, operand_weights);
        bitshift_sum.sort_unstable_by_key(|b| -(b.range_len() as isize));
        if bitshift_sum.len() == 1 {
            bitshift_sum.push(BitShiftRange(0..0, 0));
        }
        while bitshift_sum.len() > 1 {
            let first = bitshift_sum.pop().unwrap();
            let second = bitshift_sum.pop().unwrap();
            let sum = encode_bitshift_sum(first, second, bitshift_sum.is_empty(), cnf);
            if let Some(n) = bitshift_sum
                .iter()
                .position(|e| e.range_len() < sum.range_len())
            {
                bitshift_sum.insert(n, sum);
            } else {
                bitshift_sum.push(sum);
            }
        }
        bitshift_sum.pop().unwrap().into_range()
    }
}

fn input_as_bitshift_sum(
    sum_operands: &[Range<Variable>],
    operand_weights: &[usize],
) -> Vec<BitShiftRange> {
    operand_weights
        .iter()
        .zip(sum_operands.iter())
        .flat_map(|(w, r)| {
            let mut weight = *w;
            let mut shift = 0;
            let mut local_sum = Vec::new();
            loop {
                match weight {
                    0 => break local_sum.into_iter(),
                    n if n & 1 == 0 => {
                        weight >>= 1;
                        shift += 1;
                    }
                    _ => {
                        local_sum.push(BitShiftRange(r.clone(), shift));
                        weight >>= 1;
                        shift += 1;
                    }
                }
            }
        })
        .collect()
}

fn encode_bitshift_sum(
    mut bs0: BitShiftRange,
    mut bs1: BitShiftRange,
    no_shifting: bool,
    cnf: &mut CNFFormula,
) -> BitShiftRange {
    let min_shift = usize::min(bs0.shift(), bs1.shift());
    if !no_shifting && min_shift > 0 {
        bs0.decrease_shift(min_shift);
        bs1.decrease_shift(min_shift);
        let mut shifted_result = encode_bitshift_sum(bs0, bs1, no_shifting, cnf);
        shifted_result.increase_shift(min_shift);
        return shifted_result;
    }
    let n_input_bits = usize::max(bs0.n_bits(), bs1.n_bits());
    let carries = 1 + cnf.n_vars()..1 + cnf.n_vars() + n_input_bits;
    let encoding = 1 + cnf.n_vars() + n_input_bits..2 + cnf.n_vars() + (n_input_bits << 1);
    cnf.add_vars(carries.len() + encoding.len());
    for i in 0..n_input_bits {
        let input_carry = if i == 0 {
            None
        } else {
            Some(carries.start + i - 1)
        };
        let output_carry = if i == n_input_bits - 1 {
            encoding.end - 1
        } else {
            carries.start + i
        };
        sum_bits(
            bs0.bit(i),
            bs1.bit(i),
            input_carry,
            encoding.start + i,
            output_carry,
            cnf,
        );
    }
    BitShiftRange(encoding, 0)
}

fn sum_bits(
    v0: Option<Variable>,
    v1: Option<Variable>,
    v2: Option<Variable>,
    sum_bit: Variable,
    carry_bit: Variable,
    cnf: &mut CNFFormula,
) {
    let mut to_sum = [v0, v1, v2];
    to_sum.sort_unstable_by_key(|o| if o.is_some() { 0 } else { 1 });
    let a = match to_sum[0] {
        Some(n) => n as isize,
        None => return,
    };
    let b = match to_sum[1] {
        Some(n) => n as isize,
        None => {
            cnf.add_clause_unchecked(vec![-a, sum_bit as isize]);
            return;
        }
    };
    if let Some(c_usize) = to_sum[2] {
        let c = c_usize as isize;
        cnf.add_clause_unchecked(vec![-a, b, c, sum_bit as isize]);
        cnf.add_clause_unchecked(vec![a, -b, c, sum_bit as isize]);
        cnf.add_clause_unchecked(vec![a, b, -c, sum_bit as isize]);
        cnf.add_clause_unchecked(vec![-a, -b, -c, sum_bit as isize]);
        cnf.add_clause_unchecked(vec![-a, -b, carry_bit as isize]);
        cnf.add_clause_unchecked(vec![-a, -c, carry_bit as isize]);
        cnf.add_clause_unchecked(vec![-b, -c, carry_bit as isize]);
    } else {
        cnf.add_clause_unchecked(vec![-a, b, sum_bit as isize]);
        cnf.add_clause_unchecked(vec![a, -b, sum_bit as isize]);
        cnf.add_clause_unchecked(vec![-a, -b, carry_bit as isize]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::VarWeights, DiscrepancyEncoding, DistanceEncoding, DrasticDistanceEncoding,
        ToCNFFormula, Weighted,
    };

    #[test]
    fn test_encode_no_weights() {
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
            DrasticDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let mut cnf = distance_encoding.to_cnf_formula();
        let counter_variables =
            WeightedParallelCounter::encode(distance_encoding.distance_vars(), &[1, 1], &mut cnf);
        assert_eq!(2, counter_variables.len());
    }

    #[test]
    fn test_encode_var_weights() {
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
            DrasticDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let mut cnf = distance_encoding.to_cnf_formula();
        let counter_variables =
            WeightedParallelCounter::encode(distance_encoding.distance_vars(), &[1, 1], &mut cnf);
        assert_eq!(3, counter_variables.len());
    }

    #[test]
    fn test_encode_distance_weights() {
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
            DrasticDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let mut cnf = distance_encoding.to_cnf_formula();
        let counter_variables =
            WeightedParallelCounter::encode(distance_encoding.distance_vars(), &[1, 2], &mut cnf);
        assert_eq!(3, counter_variables.len());
    }

    #[test]
    fn test_encode_var_and_distance_weights() {
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
            DrasticDistanceEncoding::new(&discrepancy_encoding, var_weights_vec);
        let mut cnf = distance_encoding.to_cnf_formula();
        let counter_variables =
            WeightedParallelCounter::encode(distance_encoding.distance_vars(), &[1, 2], &mut cnf);
        assert_eq!(4, counter_variables.len());
    }
}
