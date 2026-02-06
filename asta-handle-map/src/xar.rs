use std::alloc::{self, Layout};
use std::array;
use std::cell::UnsafeCell;
use std::ptr::{self, NonNull};

/// CHUNKS must be one more than a power of 2
pub struct Xar<T, const CHUNKS: usize = 17> {
    chunks: [UnsafeCell<*mut T>; CHUNKS],
}

unsafe impl<T, const CHUNKS: usize> Send for Xar<T, CHUNKS> where T: Sync {}
unsafe impl<T, const CHUNKS: usize> Sync for Xar<T, CHUNKS> where T: Sync {}

struct ChunkMeta {
    chunk_idx: usize,
    chunk_cap: usize,
    elem_idx: usize,
}

impl<T, const CHUNKS: usize> Default for Xar<T, CHUNKS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const CHUNKS: usize> Xar<T, CHUNKS> {
    const fn shift() -> u32 {
        // chunks = 1 << (log2 PLATFORM_BITS - log2 shift) + 1
        // chunks - 1 = 1 << (log2 PLATFORM_BITS - log2 shift)
        // log2 (chunks - 1) = log2 PLATFORM_BITS - log2 shift
        // log2 PLATFORM_BITS - log2 (chunks - 1) = log2 shift
        // shift = 1 << (log2 PLATFORM_BITS - log2 (chunks - 1))
        // shift = PLATFORM_BITS / (chunks - 1)
        usize::BITS / (CHUNKS - 1) as u32
    }
    const fn meta(&self, index: usize) -> ChunkMeta {
        let index_shift = index >> Self::shift();
        if index_shift > 0 {
            let chunk_idx = usize::BITS - index_shift.leading_zeros();
            let chunk_cap = 1 << (Self::shift() + chunk_idx - 1);
            let elem_idx = index - chunk_cap;

            ChunkMeta {
                chunk_idx: chunk_idx as usize,
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
    pub fn new() -> Self {
        Self {
            chunks: array::from_fn(|_| UnsafeCell::new(ptr::null_mut())),
        }
    }
    pub fn capacity(&self) -> usize {
        let first = self
            .chunks
            .iter()
            .rposition(|ptr| !unsafe { ptr.get().read().is_null() });
        match first {
            Some(chunk_idx) => 1 << (Self::shift() as usize + chunk_idx.max(1)),
            None => 0,
        }
    }
    pub unsafe fn get(&self, index: usize) -> &T {
        let meta = self.meta(index);
        unsafe {
            NonNull::new_unchecked(self.chunks[meta.chunk_idx].get().read())
                .offset(meta.elem_idx as isize)
                .as_ref()
        }
    }
    pub unsafe fn push(&self, value: T, len: usize) {
        let meta = self.meta(len);

        let chunk_ptr = self.chunks[meta.chunk_idx].get();
        let ptr = unsafe {
            match chunk_ptr.read() {
                ptr if ptr.is_null() => {
                    let allocated =
                        alloc::alloc(Layout::array::<T>(meta.chunk_cap).unwrap()) as *mut T;
                    chunk_ptr.write(allocated);
                    NonNull::new_unchecked(allocated)
                }
                ptr => NonNull::new_unchecked(ptr),
            }
        };

        unsafe { ptr.offset(meta.elem_idx as isize).write(value) };
    }
    pub unsafe fn drop(&mut self, len: usize) {
        if len == 0 {
            return;
        }

        let meta = self.meta(len - 1);
        for (chunk_idx, chunk) in self.chunks.iter_mut().take(meta.chunk_idx + 1).enumerate() {
            let ptr = *chunk.get_mut();

            let chunk_cap = 1 << (Self::shift() as usize + chunk_idx - 1);
            let chunk_len = if chunk_idx == meta.chunk_idx {
                meta.elem_idx + 1
            } else {
                chunk_cap
            };

            unsafe {
                for idx in 0..chunk_len {
                    drop(NonNull::new_unchecked(ptr).offset(idx as isize).read())
                }
                alloc::dealloc(ptr as *mut u8, Layout::array::<T>(chunk_cap).unwrap());
            }
        }
    }
}
