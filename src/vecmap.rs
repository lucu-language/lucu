use std::{
    collections::HashMap,
    hash::Hash,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

macro_rules! vecmap_index {
    ($name:ident) => {
        #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
        pub struct $name(pub(crate) usize);

        impl From<$name> for usize {
            fn from(value: $name) -> Self {
                value.0
            }
        }
    };
}
pub(crate) use vecmap_index;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VecMap<K, V>
where
    K: Into<usize>,
{
    vec: Vec<V>,
    key: PhantomData<fn(K) -> V>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VecMapOffset<K, V>
where
    K: Into<usize>,
{
    start: usize,
    vec: Vec<V>,
    key: PhantomData<fn(K) -> V>,
}

#[derive(Debug, Clone)]
pub struct VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Clone,
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

impl<K, V> Default for VecMapOffset<K, V>
where
    K: Into<usize>,
{
    fn default() -> Self {
        Self::new(0)
    }
}

impl<K, V> Default for VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Clone,
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

impl<K, V> From<VecMapOffset<K, V>> for Vec<V>
where
    K: Into<usize>,
{
    fn from(value: VecMapOffset<K, V>) -> Self {
        value.vec
    }
}

impl<K, V> FromIterator<V> for VecMap<K, V>
where
    K: Into<usize>,
{
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl<K, V> VecMapOffset<K, V>
where
    K: Into<usize>,
{
    pub fn new(start: usize) -> Self {
        Self {
            start,
            vec: Vec::new(),
            key: PhantomData,
        }
    }
    pub fn from_iter(start: usize, iter: impl IntoIterator<Item = V>) -> Self {
        Self {
            start,
            vec: Vec::from_iter(iter),
            key: PhantomData,
        }
    }
    pub fn start(&self) -> usize {
        self.start
    }
    pub fn push(&mut self, f: impl FnOnce(usize) -> K, value: V) -> K {
        let k = f(self.vec.len() + self.start);
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
        (self.start..self.len() + self.start).map(f)
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
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }
    // from https://stackoverflow.com/a/74296885
    pub fn get_mut2(&mut self, i: K, j: K) -> Option<(&mut V, &mut V)> {
        let i: usize = i.into() - self.start;
        let j: usize = j.into() - self.start;
        if i == j {
            return None;
        }
        let (start, end) = if i < j { (i, j) } else { (j, i) };
        let (first, second) = self.vec.split_at_mut(start + 1);
        let (first, second) = (&mut first[start], &mut second[end - start - 1]);

        if i < j {
            Some((first, second))
        } else {
            Some((second, first))
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
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
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
        let (first, second) = (&mut first[start], &mut second[end - start - 1]);

        if i < j {
            Some((first, second))
        } else {
            Some((second, first))
        }
    }
}

impl<K, V> VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Clone,
{
    pub fn new() -> Self {
        Self {
            vec: VecMap::new(),
            set: HashMap::new(),
        }
    }
    pub fn insert(&mut self, f: impl FnOnce(usize) -> K, value: V) -> &K {
        if !self.set.contains_key(&value) {
            self.set.insert(value.clone(), self.vec.push(f, value));
            let value = self.vec.vec.last().unwrap();
            &self.set[value]
        } else {
            &self.set[&value]
        }
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.vec.values()
    }
    pub fn keys(&self, f: impl Fn(usize) -> K) -> impl Iterator<Item = K> {
        self.vec.keys(f)
    }
    pub fn iter(&self, f: impl Fn(usize) -> K) -> impl Iterator<Item = (K, &V)> {
        self.vec.iter(f)
    }
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
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

impl<K, V> Index<K> for VecMapOffset<K, V>
where
    K: Into<usize>,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        &self.vec[index.into() - self.start]
    }
}

impl<K, V> IndexMut<K> for VecMapOffset<K, V>
where
    K: Into<usize>,
{
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.vec[index.into() - self.start]
    }
}

impl<K, V> Index<K> for VecSet<K, V>
where
    K: Into<usize>,
    V: Hash + Eq + Clone,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        &self.vec[index]
    }
}
