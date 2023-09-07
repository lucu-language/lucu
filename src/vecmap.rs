use std::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

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
        Self {
            vec: Vec::new(),
            key: PhantomData,
        }
    }
}

impl<K, V> VecMap<K, V>
where
    K: Into<usize>,
{
    pub fn push(&mut self, f: impl FnOnce(usize) -> K, value: V) -> K {
        let k = f(self.vec.len());
        self.vec.push(value);
        k
    }
    pub fn iter(&self) -> impl Iterator<Item = &V> {
        self.vec.iter()
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
