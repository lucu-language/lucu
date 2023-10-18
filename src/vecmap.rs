use std::{
    collections::HashMap,
    hash::Hash,
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

#[derive(Debug)]
pub struct VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Copy,
{
    vec: VecMap<K, V>,
    set: HashMap<V, K>,
}

impl<K, V> Default for VecMap<K, V>
where
    K: Into<usize>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Default for VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Copy,
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
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.vec.iter_mut()
    }
    pub fn keys(&self, f: impl Fn(usize) -> K) -> impl Iterator<Item = K> {
        (0..self.len()).map(f)
    }
    pub fn iter(&self, f: impl Fn(usize) -> K) -> impl Iterator<Item = (K, &V)> {
        self.keys(f).zip(self.values())
    }
    pub fn iter_mut(&mut self, f: impl Fn(usize) -> K) -> impl Iterator<Item = (K, &mut V)> {
        self.keys(f).zip(self.values_mut())
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    // from https://stackoverflow.com/a/74296885
    pub fn get_mut2(&mut self, i: K, j: K) -> Option<(&mut V, &mut V)> {
        let i: usize = i.into();
        let j: usize = j.into();
        if i == j {
            return None;
        }
        let (start, end) = if i < j { (i, j) } else { (j, i) };

        let (first, second) = self.vec.split_at_mut(start + 1);
        Some((&mut first[start], &mut second[end - start - 1]))
    }
}

impl<K, V> VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Copy,
{
    pub fn new() -> Self {
        Self {
            vec: VecMap::new(),
            set: HashMap::new(),
        }
    }
    pub fn insert(&mut self, f: impl FnOnce(usize) -> K, value: V) -> &K {
        if !self.set.contains_key(&value) {
            self.set.insert(value, self.vec.push(f, value));
        }
        &self.set[&value]
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.vec.values()
    }
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.vec.values_mut()
    }
    pub fn keys(&self, f: impl Fn(usize) -> K) -> impl Iterator<Item = K> {
        self.vec.keys(f)
    }
    pub fn iter(&self, f: impl Fn(usize) -> K) -> impl Iterator<Item = (K, &V)> {
        self.vec.iter(f)
    }
    pub fn iter_mut(&mut self, f: impl Fn(usize) -> K) -> impl Iterator<Item = (K, &mut V)> {
        self.vec.iter_mut(f)
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

impl<K, V> Index<K> for VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Copy,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        &self.vec[index]
    }
}

impl<K, V> IndexMut<K> for VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Copy,
{
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.vec[index]
    }
}
