use std::hash::{BuildHasher, Hash, RandomState};
use std::sync::RwLock;

use hashbrown::Equivalent;
use hashbrown::hash_table::HashTable;

use crate::xar::XarInner;

pub mod xar;

pub struct HandleMap<K, V, const BITS: u32 = 24, const CHUNKS: usize = 16, S = RandomState> {
    indices: RwLock<HashTable<u32>>,
    entries: XarInner<(K, V), BITS, CHUNKS>,
    hash_builder: S,
}

pub struct HandleSet<T, const BITS: u32 = 24, const CHUNKS: usize = 16, S = RandomState>(
    HandleMap<T, (), BITS, CHUNKS, S>,
);

impl<K, V, const BITS: u32, const CHUNKS: usize, S> Drop for HandleMap<K, V, BITS, CHUNKS, S> {
    fn drop(&mut self) {
        unsafe { self.entries.drop(self.len()) };
    }
}

impl<K, V, const BITS: u32, const CHUNKS: usize, S> Default for HandleMap<K, V, BITS, CHUNKS, S>
where
    S: Default,
{
    fn default() -> Self {
        Self {
            indices: Default::default(),
            entries: Default::default(),
            hash_builder: Default::default(),
        }
    }
}

impl<T, const BITS: u32, const CHUNKS: usize, S> Default for HandleSet<T, BITS, CHUNKS, S>
where
    S: Default,
{
    fn default() -> Self {
        Self(HandleMap::default())
    }
}

impl<K, V, const BITS: u32, const CHUNKS: usize, S> HandleMap<K, V, BITS, CHUNKS, S> {
    pub fn new() -> Self
    where
        S: Default,
    {
        Self::default()
    }
    pub fn with_hasher(hash_builder: S) -> Self {
        Self {
            indices: Default::default(),
            entries: Default::default(),
            hash_builder,
        }
    }
    pub fn get_or_insert(&self, key: K, insert: impl FnOnce(u32) -> V) -> (u32, &V)
    where
        K: Hash + Equivalent<K>,
        S: BuildHasher,
    {
        let hash = self.hash_builder.hash_one(&key);

        // GET
        let indices = self.indices.read().unwrap();
        let old_index = indices.len() as u32;

        {
            let search = indices
                .find(hash, |&i| {
                    K::equivalent(&key, unsafe { self.get_unchecked(i) }.0)
                })
                .copied();
            if let Some(i) = search {
                return (i, unsafe { self.get_unchecked(i) }.1);
            }
        }
        drop(indices);

        // INSERT
        let mut indices = self.indices.write().unwrap();
        let index = indices.len() as u32;

        if old_index != index {
            // Some new stuff got inserted between our first check and now.
            // Luckily, we have unique write access at the moment,
            // so we just do another check to make sure there's no race condition.
            let search = indices
                .find(hash, |&i| {
                    K::equivalent(&key, unsafe { self.get_unchecked(i) }.0)
                })
                .copied();
            if let Some(i) = search {
                return (i, unsafe { self.get_unchecked(i) }.1);
            }
        }

        let (_, value) = unsafe { self.entries.push((key, insert(index)), index) };
        indices.insert_unique(hash, index, |&i| {
            self.hash_builder
                .hash_one(&unsafe { self.entries.get(i) }.0)
        });

        (index, value)
    }
    pub fn get_index_of<Q>(&self, key: &Q) -> Option<u32>
    where
        Q: ?Sized + Hash + Equivalent<K>,
        S: BuildHasher,
    {
        let indices = self.indices.read().unwrap();
        let hash = self.hash_builder.hash_one(key);
        indices
            .find(hash, |&i| {
                Q::equivalent(key, unsafe { self.get_unchecked(i) }.0)
            })
            .copied()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn len(&self) -> u32 {
        self.indices.read().unwrap().len() as u32
    }
    pub fn capacity(&self) -> u32 {
        self.entries.capacity()
    }
    pub fn get(&self, index: u32) -> Option<(&K, &V)> {
        (index < self.len()).then(|| unsafe { self.get_unchecked(index) })
    }
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        (0..self.len()).map(|idx| unsafe { self.get_unchecked(idx) })
    }
    pub unsafe fn get_unchecked(&self, index: u32) -> (&K, &V) {
        let (k, v) = unsafe { self.entries.get(index) };
        (k, v)
    }
}

impl<T, const BITS: u32, const CHUNKS: usize, S> HandleSet<T, BITS, CHUNKS, S> {
    pub fn new() -> Self
    where
        S: Default,
    {
        Self::default()
    }
    pub fn with_hasher(hash_builder: S) -> Self {
        Self(HandleMap::with_hasher(hash_builder))
    }
    pub fn insert(&self, value: T) -> u32
    where
        T: Hash + Equivalent<T>,
        S: BuildHasher,
    {
        self.0.get_or_insert(value, |_| ()).0
    }
    pub fn get_index_of<Q>(&self, key: &Q) -> Option<u32>
    where
        Q: ?Sized + Hash + Equivalent<T>,
        S: BuildHasher,
    {
        self.0.get_index_of(key)
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn len(&self) -> u32 {
        self.0.len()
    }
    pub fn capacity(&self) -> u32 {
        self.0.capacity()
    }
    pub fn get(&self, index: u32) -> Option<&T> {
        self.0.get(index).map(|(t, _)| t)
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter().map(|(t, _)| t)
    }
    pub unsafe fn get_unchecked(&self, index: u32) -> &T {
        unsafe { self.0.get_unchecked(index) }.0
    }
}
