use std::hash::{BuildHasher, Hash, RandomState};
use std::sync::RwLock;

use hashbrown::Equivalent;
use hashbrown::hash_table::HashTable;

use crate::xar::Xar;

pub mod xar;

pub struct HandleMap<T, S = RandomState> {
    indices: RwLock<HashTable<u32>>,
    entries: Xar<T>,
    hash_builder: S,
}

impl<T, S> Drop for HandleMap<T, S> {
    fn drop(&mut self) {
        unsafe { self.entries.drop(self.len()) };
    }
}

impl<T, S> Default for HandleMap<T, S>
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

impl<T, S> HandleMap<T, S> {
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
    pub fn insert(&self, value: T) -> u32
    where
        T: Hash + Equivalent<T>,
        S: BuildHasher,
    {
        match self.get_index_of(&value) {
            Some(idx) => idx,
            None => {
                let hash = self.hash_builder.hash_one(&value);

                let mut indices = self.indices.write().unwrap();
                let index = indices.len() as u32;
                unsafe { self.entries.push(value, index) };
                indices.insert_unique(hash, index, |&i| {
                    self.hash_builder.hash_one(unsafe { self.entries.get(i) })
                });

                index
            }
        }
    }
    pub fn get_index_of<Q>(&self, key: &Q) -> Option<u32>
    where
        Q: ?Sized + Hash + Equivalent<T>,
        S: BuildHasher,
    {
        let indices = self.indices.read().unwrap();
        let hash = self.hash_builder.hash_one(key);
        indices
            .find(hash, |&i| {
                Q::equivalent(key, unsafe { self.get_unchecked(i) })
            })
            .copied()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn len(&self) -> u32 {
        self.indices.read().unwrap().len() as u32
    }
    pub fn get(&self, index: u32) -> Option<&T> {
        (index < self.len()).then(|| unsafe { self.get_unchecked(index) })
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        (0..self.len()).map(|idx| unsafe { self.get_unchecked(idx) })
    }
    pub unsafe fn get_unchecked(&self, index: u32) -> &T {
        unsafe { self.entries.get(index) }
    }
}
