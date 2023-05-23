use crate::Variable;
use std::{
    cell::{Ref, RefCell},
    ops::{Deref, Index},
};

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Weighted<T> {
    weight: usize,
    thing: T,
}

impl<T> Weighted<T> {
    pub fn new(thing: T, weight: usize) -> Self {
        Self { weight, thing }
    }

    pub fn thing(&self) -> &T {
        &self.thing
    }

    pub fn weight(&self) -> usize {
        self.weight
    }
}

pub struct VarWeights {
    weights: Vec<Option<Weighted<Variable>>>,
    max_weight: Option<usize>,
    weights_sorted_dedup_cache: RefCell<Option<Vec<usize>>>,
}

impl VarWeights {
    pub fn new(n_vars: usize) -> Self {
        Self {
            weights: vec![None; n_vars],
            max_weight: None,
            weights_sorted_dedup_cache: RefCell::new(Some(Vec::new())),
        }
    }

    pub fn add(&mut self, weighted_var: Weighted<Variable>) {
        self.weights[*weighted_var.thing() - 1] = Some(weighted_var);
        self.max_weight = Some(match self.max_weight {
            Some(n) if n >= weighted_var.weight() => n,
            _ => weighted_var.weight(),
        });
        *self.weights_sorted_dedup_cache.borrow_mut() = None;
    }

    pub fn iter(&self) -> impl Iterator<Item = Weighted<Variable>> + '_ {
        self.weights.iter().filter_map(|o| *o)
    }

    pub fn max_weight(&self) -> Option<usize> {
        self.max_weight
    }

    pub fn weights_sorted_dedup(&self) -> impl Deref<Target = [usize]> + '_ {
        if self.weights_sorted_dedup_cache.borrow().is_none() {
            let mut weights = self
                .weights
                .iter()
                .filter_map(|opt| opt.map(|w| w.weight()))
                .collect::<Vec<usize>>();
            weights.sort_unstable();
            weights.dedup();
            *self.weights_sorted_dedup_cache.borrow_mut() = Some(weights);
        }
        Ref::map(self.weights_sorted_dedup_cache.borrow(), |b| {
            b.as_ref().unwrap().as_slice()
        })
    }
}

impl Index<Variable> for VarWeights {
    type Output = Option<Weighted<Variable>>;

    fn index(&self, var: Variable) -> &Self::Output {
        &self.weights[var - 1]
    }
}
