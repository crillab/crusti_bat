use crate::{
    AggregatorEncoding, CNFFormula, DistanceEncoding, Literal, MaxSatSolver, ToCNFFormula,
    Variable, Weighted,
};
use anyhow::Result;
use pblib_rs::PB2CNF;
use std::{fmt::Display, ops::Range};

pub struct LeximaxAggregatorEncoding<'a> {
    maxsat_solver: Box<dyn MaxSatSolver>,
    distance_encoding: &'a dyn DistanceEncoding,
    distance_weights: &'a [usize],
    new_clauses: CNFFormula,
    bounds_vars: Vec<Range<usize>>,
}

impl<'a> LeximaxAggregatorEncoding<'a> {
    pub fn new(
        distance_encoding: &'a dyn DistanceEncoding,
        distance_weights: &'a [usize],
        maxsat_solver: Box<dyn MaxSatSolver>,
    ) -> Self {
        let mut new_clauses = CNFFormula::default();
        new_clauses.add_vars(distance_encoding.n_vars());
        let bounds_vars = encode_bounds(&mut new_clauses, distance_encoding, distance_weights);
        LeximaxAggregatorEncoding {
            maxsat_solver,
            distance_encoding,
            distance_weights,
            new_clauses,
            bounds_vars,
        }
    }
}

impl ToCNFFormula for LeximaxAggregatorEncoding<'_> {
    fn to_cnf_formula(&self) -> CNFFormula {
        let mut cnf = self.distance_encoding.to_cnf_formula();
        self.new_clauses.clone().merge_into(&mut cnf);
        cnf
    }

    fn n_vars(&self) -> usize {
        self.new_clauses.n_vars()
    }
}

#[derive(Default)]
pub struct LeximaxAggregation {
    values: Vec<(usize, usize)>,
    literals: Vec<Literal>,
}

impl Display for LeximaxAggregation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            self.values
                .iter()
                .map(|(v, w)| format!("{} (weight={})", v, w))
                .fold(String::new(), |mut acc, x| if acc.is_empty() {
                    x
                } else {
                    acc.push_str(", ");
                    acc.push_str(&x);
                    acc
                })
        )
    }
}

impl AggregatorEncoding<LeximaxAggregation> for LeximaxAggregatorEncoding<'_> {
    fn distance_encoding(&self) -> &dyn DistanceEncoding {
        self.distance_encoding
    }

    fn compute_optimum(&mut self) -> Result<LeximaxAggregation> {
        let mut cnf = self.to_cnf_formula();
        let mut result = LeximaxAggregation::default();
        self.bounds_vars.iter().for_each(|b| {
            let soft_clauses = b
                .clone()
                .enumerate()
                .map(|(i, v)| Weighted::new(vec![-(v as isize)], 1 << i))
                .collect::<Vec<_>>();
            let (value, model) = self.maxsat_solver.solve(&cnf, &soft_clauses).unwrap();
            let dv_factor = distance_vars_factors(self.distance_weights);
            result.values.push((value / dv_factor, value % dv_factor));
            b.clone().for_each(|v| {
                cnf.add_clause_unchecked(vec![model[v - 1]]);
                result.literals.push(model[v - 1])
            });
        });
        Ok(result)
    }

    fn enforce_value(&mut self, value: LeximaxAggregation) -> CNFFormula {
        let mut cnf = self.to_cnf_formula();
        value
            .literals
            .iter()
            .for_each(|l| cnf.add_clause_unchecked(vec![*l]));
        cnf
    }
}

fn encode_bounds(
    cnf: &mut CNFFormula,
    distance_encoding: &dyn DistanceEncoding,
    distance_weights: &[usize],
) -> Vec<Range<Variable>> {
    let dv_factor = distance_vars_factors(distance_weights);
    let distance_vars = distance_encoding.distance_vars();
    let backdoor_factor = (1 + distance_vars
        .iter()
        .map(|r| (1 << (r.end - r.start + 1)) - 1)
        .sum::<usize>())
        * dv_factor;
    let max_bound_value = (1 + distance_vars
        .iter()
        .map(|r| (1 << (r.end - r.start + 1)) - 1)
        .max()
        .unwrap_or_default())
        * dv_factor;
    let bound_n_vars = f64::ceil(f64::log2(max_bound_value as f64)) as usize;
    (0..distance_vars.len())
        .map(|i| {
            encode_bound(
                cnf,
                i,
                bound_n_vars,
                distance_vars,
                distance_weights,
                dv_factor,
                backdoor_factor,
            )
        })
        .collect()
}

fn encode_bound(
    cnf: &mut CNFFormula,
    bound_index: usize,
    bound_n_vars: usize,
    distance_vars: &[Range<Variable>],
    distance_weights: &[usize],
    value_factor: usize,
    backdoor_factor: usize,
) -> Range<Variable> {
    let bound_vars = cnf.n_vars() + 1..cnf.n_vars() + 1 + bound_n_vars;
    cnf.add_vars(bound_n_vars);
    let backdoor_vars = cnf.n_vars() + 1..cnf.n_vars() + 1 + distance_vars.len();
    cnf.add_vars(distance_vars.len());
    let pb2cnf = PB2CNF::default();
    distance_vars.iter().enumerate().for_each(|(i, dv)| {
        let literals = bound_vars
            .clone()
            .chain(dv.clone())
            .chain(std::iter::once(backdoor_vars.start + i))
            .map(|i| i as i32)
            .collect();
        let weights = (0..bound_n_vars)
            .map(|i| 1 << i)
            .chain((0..dv.len()).map(|i| -(value_factor as i64 * (1 << i) as i64)))
            .chain(std::iter::once(backdoor_factor as i64))
            .collect();
        let first_aux_var = 1 + cnf.n_vars() as i32;
        let encoding =
            pb2cnf.encode_geq(weights, literals, distance_weights[i] as i64, first_aux_var);
        cnf.add_vars((encoding.next_free_var_id() - first_aux_var) as usize);
        encoding.clauses().iter().for_each(|clause| {
            cnf.add_clause_unchecked(clause.iter().map(|l| *l as isize).collect());
        });
    });
    let first_aux_var = 1 + cnf.n_vars() as i32;
    let encoding = pb2cnf.encode_at_most_k(
        backdoor_vars.clone().map(|i| i as i32).collect(),
        bound_index as i64,
        first_aux_var,
    );
    cnf.add_vars((encoding.next_free_var_id() - first_aux_var) as usize);
    encoding.clauses().iter().for_each(|clause| {
        cnf.add_clause_unchecked(clause.iter().map(|l| *l as isize).collect());
    });
    bound_vars
}

fn distance_vars_factors(distance_weights: &[usize]) -> usize {
    1 + distance_weights.iter().sum::<usize>()
}
