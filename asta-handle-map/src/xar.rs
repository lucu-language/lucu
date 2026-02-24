use std::alloc::{self, Layout};
use std::array;
use std::cell::UnsafeCell;
use std::ptr::{self, NonNull};
use std::sync::RwLock;

pub struct Xar<T, const BITS: u32 = 24, const CHUNKS: usize = 16> {
    inner: XarInner<T, BITS, CHUNKS>,
    // TODO: we could even have a lock ONLY for pushing when we need to allocate
    // add optional mutex lock parameter to XarInner::push
    len: RwLock<u32>,
}

impl<T, const BITS: u32, const CHUNKS: usize> Drop for Xar<T, BITS, CHUNKS> {
    fn drop(&mut self) {
        unsafe { self.inner.drop(*self.len.get_mut().unwrap()) };
    }
}

impl<T, const BITS: u32, const CHUNKS: usize> Default for Xar<T, BITS, CHUNKS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const BITS: u32, const CHUNKS: usize> Xar<T, BITS, CHUNKS> {
    pub fn new() -> Self {
        Self {
            inner: XarInner::new(),
            len: RwLock::new(0),
        }
    }
    pub fn capacity(&self) -> u32 {
        self.inner.capacity()
    }
    pub fn len(&self) -> u32 {
        *self.len.read().unwrap()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn get(&self, idx: u32) -> Option<&T> {
        (idx < self.len()).then(|| unsafe { self.get_unchecked(idx) })
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        (0..self.len()).map(|idx| unsafe { self.get_unchecked(idx) })
    }
    pub unsafe fn get_unchecked(&self, idx: u32) -> &T {
        unsafe { self.inner.get(idx) }
    }
    pub fn push(&self, t: T) -> u32 {
        let mut len = self.len.write().unwrap();
        let idx = *len;
        unsafe { self.inner.push(t, *len) };
        *len += 1;
        idx
    }
}

pub(crate) struct XarInner<T, const BITS: u32, const CHUNKS: usize> {
    chunks: [UnsafeCell<*mut T>; CHUNKS],
}

unsafe impl<T, const BITS: u32, const CHUNKS: usize> Send for XarInner<T, BITS, CHUNKS> where T: Sync
{}
unsafe impl<T, const BITS: u32, const CHUNKS: usize> Sync for XarInner<T, BITS, CHUNKS> where T: Sync
{}

struct ChunkMeta {
    chunk_idx: u32,
    chunk_cap: u32,
    elem_idx: u32,
}

impl<T, const BITS: u32, const CHUNKS: usize> Default for XarInner<T, BITS, CHUNKS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const BITS: u32, const CHUNKS: usize> XarInner<T, BITS, CHUNKS> {
    const fn shift() -> u32 {
        BITS - (CHUNKS as u32 - 1)
    }
    const fn meta(&self, index: u32) -> ChunkMeta {
        let index_shift = index >> Self::shift();
        if index_shift > 0 {
            let chunk_idx = 32 - index_shift.leading_zeros();
            let chunk_cap = 1 << (Self::shift() + chunk_idx - 1);
            let elem_idx = index - chunk_cap;

            ChunkMeta {
                chunk_idx,
                chunk_cap,
                elem_idx,
            }
        } else {
            ChunkMeta {
                chunk_idx: 0,
                chunk_cap: 1 << Self::shift(),
                elem_idx: index,
            }
        }
    }
    pub(crate) fn new() -> Self {
        Self {
            chunks: array::from_fn(|_| UnsafeCell::new(ptr::null_mut())),
        }
    }
    pub(crate) fn capacity(&self) -> u32 {
        let first = self
            .chunks
            .iter()
            .rposition(|ptr| unsafe { !ptr.get().read().is_null() });
        match first {
            Some(chunk_idx) => 1 << (Self::shift() as usize + chunk_idx),
            None => 0,
        }
    }
    pub(crate) unsafe fn get(&self, index: u32) -> &T {
        let meta = self.meta(index);
        unsafe {
            NonNull::new_unchecked(self.chunks[meta.chunk_idx as usize].get().read())
                .offset(meta.elem_idx as isize)
                .as_ref()
        }
    }
    pub(crate) unsafe fn push(&self, value: T, len: u32) {
        let meta = self.meta(len);

        let chunk_ptr = self.chunks[meta.chunk_idx as usize].get();
        let ptr = unsafe {
            match chunk_ptr.read() {
                ptr if ptr.is_null() => {
                    let allocated =
                        alloc::alloc(Layout::array::<T>(meta.chunk_cap as usize).unwrap())
                            as *mut T;
                    chunk_ptr.write(allocated);
                    NonNull::new_unchecked(allocated)
                }
                ptr => NonNull::new_unchecked(ptr),
            }
        };

        unsafe { ptr.offset(meta.elem_idx as isize).write(value) };
    }
    pub(crate) unsafe fn drop(&mut self, len: u32) {
        if len == 0 {
            return;
        }

        let meta = self.meta(len - 1);
        for (chunk_idx, chunk) in self
            .chunks
            .iter_mut()
            .take(meta.chunk_idx as usize + 1)
            .enumerate()
        {
            let ptr = *chunk.get_mut();

            let chunk_cap = 1 << (Self::shift() as usize + chunk_idx.max(1) - 1);
            let chunk_len = if chunk_idx as u32 == meta.chunk_idx {
                meta.elem_idx + 1
            } else {
                chunk_cap
            };

            unsafe {
                for idx in 0..chunk_len {
                    drop(NonNull::new_unchecked(ptr).offset(idx as isize).read())
                }
                alloc::dealloc(
                    ptr as *mut u8,
                    Layout::array::<T>(chunk_cap as usize).unwrap(),
                );
            }
        }
    }
}
