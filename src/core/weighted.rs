use crate::Variable;
use std::{
    cell::{Ref, RefCell},
    ops::{Deref, Index},
};

/// A thing with a weight.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Weighted<T> {
    weight: usize,
    thing: T,
}

impl<T> Weighted<T> {
    /// Builds a new weighted thing.
    pub fn new(thing: T, weight: usize) -> Self {
        Self { weight, thing }
    }

    /// Returns a reference to the thing.
    pub fn thing(&self) -> &T {
        &self.thing
    }

    /// Consumes this object, returning the underlying thing.
    pub fn into_thing(self) -> T {
        self.thing
    }

    /// Returns the weight of the thing.
    pub fn weight(&self) -> usize {
        self.weight
    }
}

/// A structure used to handle the weights of the whole set of variables of a formula.
///
/// The structure is initialized with the number of variables involved in the formula.
/// When requesting a variable for which no weight has been associated with, `None` is returned.
/// Requesting a variable with an index higher than the given number of variables panics.
pub struct VarWeights {
    weights: Vec<Option<Weighted<Variable>>>,
    max_weight: Option<usize>,
    weights_sorted_dedup_cache: RefCell<Option<Vec<usize>>>,
}

impl VarWeights {
    /// Builds a new instance of this structure.
    pub fn new(n_vars: usize) -> Self {
        Self {
            weights: vec![None; n_vars],
            max_weight: None,
            weights_sorted_dedup_cache: RefCell::new(Some(Vec::new())),
        }
    }

    /// Associates a weight with a variable.
    ///
    /// # Panics
    ///
    /// This function panics if the parameter involves a variables which index is higher than the number of variables defined at the structure initialization.
    pub fn add(&mut self, weighted_var: Weighted<Variable>) {
        self.weights[*weighted_var.thing() - 1] = Some(weighted_var);
        self.max_weight = Some(match self.max_weight {
            Some(n) if n >= weighted_var.weight() => n,
            _ => weighted_var.weight(),
        });
        *self.weights_sorted_dedup_cache.borrow_mut() = None;
    }

    /// Iterates over the (weighted) variables which have a weight associated with.
    pub fn iter(&self) -> impl Iterator<Item = Weighted<Variable>> + '_ {
        self.weights.iter().filter_map(|o| *o)
    }

    /// Returns the maximal weight associated with a variable, or `None` if none.
    pub fn max_weight(&self) -> Option<usize> {
        self.max_weight
    }

    /// Returns the set of weights associated with variables in ascending order.
    /// Same weights are not repeated.
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
