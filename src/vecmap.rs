use std::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

#[derive(Debug)]
pub struct VecMap<K, V>
where
    K: Into<usize>,
{
    vec: Vec<V>,
    key: PhantomData<fn(K) -> V>,
}

impl<K, V> Default for VecMap<K, V>
where
    K: Into<usize>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> From<Vec<V>> for VecMap<K, V>
where
    K: Into<usize>,
{
    fn from(value: Vec<V>) -> Self {
        Self {
            vec: value,
            key: PhantomData,
        }
    }
}

impl<K, V> From<VecMap<K, V>> for Vec<V>
where
    K: Into<usize>,
{
    fn from(value: VecMap<K, V>) -> Self {
        value.vec
    }
}

impl<K, V> VecMap<K, V>
where
    K: Into<usize>,
{
    pub fn new() -> Self {
        Self {
            vec: Vec::new(),
            key: PhantomData,
        }
    }
    pub fn push(&mut self, f: impl FnOnce(usize) -> K, value: V) -> K {
        let k = f(self.vec.len());
        self.vec.push(value);
        k
    }
    pub fn push_value(&mut self, value: V) {
        self.vec.push(value);
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.vec.iter()
    }
    pub fn keys(&self, f: impl Fn(usize) -> K) -> impl Iterator<Item = K> {
        (0..self.len()).map(f)
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
}

impl<K, V> VecMap<K, V>
where
    K: Into<usize>,
    V: Clone,
{
    pub fn filled(n: usize, val: V) -> Self {
        Self {
            vec: vec![val; n],
            key: PhantomData,
        }
    }
}

impl<K, V> Index<K> for VecMap<K, V>
where
    K: Into<usize>,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        &self.vec[index.into()]
    }
}

impl<K, V> IndexMut<K> for VecMap<K, V>
where
    K: Into<usize>,
{
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.vec[index.into()]
    }
}
