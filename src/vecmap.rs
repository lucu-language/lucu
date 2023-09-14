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
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.vec.iter()
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    pub fn as_vec(self) -> Vec<V> {
        self.vec
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
