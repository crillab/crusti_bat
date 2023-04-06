#[derive(Clone, Debug, PartialEq, Eq)]
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
