#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use std::{marker::PhantomPinned, mem::{self, MaybeUninit}, pin::Pin, ptr::NonNull};

use const_assert::{Assert, IsTrue};


#[derive(Debug, Clone, Copy)]
pub enum FreeError {

    NullPtrFree,
    DoubleFree,
    FreeOutOfBounds,
    UnalignedFree,

}


pub struct FixedSizeAllocator<const S: usize, const N: usize> {

    memory: [MaybeUninit<[u8; S]>; N],

    free_table: [bool; N],

    total_free: usize,

    upper_heap_bound: NonNull<u8>,

    _pin: PhantomPinned

}

impl<const S: usize, const N: usize> FixedSizeAllocator<S, N> 
where 
    Assert<{ S > 0 }>: IsTrue
{

    pub unsafe fn new_unpinned_uninitialized(zero_initialized: bool) -> Self {

        let memory = if zero_initialized {
            [MaybeUninit::zeroed(); N]
        } else {
            [MaybeUninit::uninit(); N]
        };

        Self {
            memory,
            free_table: [true; N],
            total_free: S * N,
            upper_heap_bound: NonNull::dangling(),
            _pin: Default::default()
        }
    }


    pub unsafe fn init_bounds(self: Pin<&mut Self>) {
        
        let self_data = unsafe { self.get_unchecked_mut() };

        self_data.upper_heap_bound = unsafe {
            NonNull::new_unchecked(self_data.memory.as_ptr().byte_add(S * N) as *mut u8)
        };
    } 


    pub fn new(zero_initialized: bool) -> Pin<Box<Self>> {
        
        let mut res = Box::new( unsafe {
            Self::new_unpinned_uninitialized(zero_initialized)
        });

        res.upper_heap_bound = unsafe {
            NonNull::new_unchecked(res.memory.as_ptr().byte_add(S * N) as *mut u8)
        };

        Box::into_pin(res)
    }


    pub const fn heap_size(&self) -> usize {
        S * N
    }


    pub const fn block_count(&self) -> usize {
        N
    }


    pub const fn block_size(&self) -> usize {
        S
    }


    pub const fn total_free(&self) -> usize {
        self.total_free
    }


    pub const fn total_allocated(&self) -> usize {
        self.heap_size() - self.total_free()
    }


    pub fn free_blocks(&self) -> usize {
        self.free_table
            .iter()
            .filter(|&&is_free| is_free)
            .count()
    }


    pub fn allocated_blocks(&self) -> usize {
        N - self.free_blocks()
    }


    pub fn alloc<T>(self: Pin<&mut Self>) -> Option<NonNull<T>>
    where 
        Assert<{ mem::size_of::<T>() == S }>: IsTrue
    {
        let self_data = unsafe { self.get_unchecked_mut() };

        if self_data.total_free() == 0 {
            None
        } else {
            
            let mut left = 0;
            let mut right = self_data.free_table.len() - 1;

            while left <= right {

                if self_data.free_table[left] {
                    self_data.total_free -= self_data.block_size();
                    self_data.free_table[left] = false;
                    return Some(self_data.real_ptr_from_block_index(left));
                }

                if self_data.free_table[right] {
                    self_data.total_free -= self_data.block_size();
                    self_data.free_table[right] = false;
                    return Some(self_data.real_ptr_from_block_index(right));
                }

                left += 1;
                right -= 1;
            }

            None
        }
    }


    fn real_ptr_from_block_index<T>(&self, block_index: usize) -> NonNull<T> {
        unsafe {
            NonNull::new_unchecked(
                self.memory.as_ptr().add(block_index) as *mut T
            )
        }
    }


    fn block_index_from_real_ptr<T>(&self, ptr: NonNull<T>) -> Result<usize, FreeError> {

        if (ptr.as_ptr() as usize) < (self.memory.as_ptr() as usize) || (ptr.as_ptr() as usize) >= (self.upper_heap_bound.as_ptr() as usize) {
            return Err(FreeError::FreeOutOfBounds)
        }

        let offset = if let Some(offset) = (ptr.as_ptr() as usize).checked_sub(self.memory.as_ptr() as usize) {
            offset
        } else {
            return Err(FreeError::FreeOutOfBounds);
        };

        if offset % self.block_size() != 0 {
            Err(FreeError::UnalignedFree)
        } else {
            Ok(
                offset / self.block_size()
            )
        }
    }


    pub fn free_nonnull<T>(self: Pin<&mut Self>, ptr: NonNull<T>) -> Result<(), FreeError> 
    where 
        Assert<{ mem::size_of::<T>() == S }>: IsTrue
    {
        let self_data = unsafe { self.get_unchecked_mut() };

        let block_index = self_data.block_index_from_real_ptr(ptr)?;

        if self_data.free_table[block_index] {
            Err(FreeError::DoubleFree)
        } else {
            self_data.free_table[block_index] = true;
            self_data.total_free += self_data.block_size();
            Ok(())
        }
    }


    pub fn free<T>(self: Pin<&mut Self>, ptr: *const T) -> Result<(), FreeError> 
    where
        Assert<{ mem::size_of::<T>() == S }>: IsTrue
    {
        if let Some(ptr) = NonNull::new(ptr as *mut T) {
            self.free_nonnull(ptr)
        } else {
            Err(FreeError::NullPtrFree)
        }
    }

}


#[cfg(test)]
mod tests {

    use std::pin::pin;

    use super::*;


    #[test]
    fn check_new() {

        let alloc = FixedSizeAllocator::<8, 64>::new(false);

        assert_eq!(alloc.block_size(), 8);
        assert_eq!(alloc.heap_size(), 64*8);
        assert_eq!(alloc.block_count(), 64);
        assert_eq!(alloc.free_blocks(), 64);
        assert_eq!(alloc.allocated_blocks(), 0);
        assert_eq!(alloc.total_allocated(), 0);
        assert_eq!(alloc.total_free(), alloc.heap_size());
    }


    #[test]
    fn check_alloc() {

        let mut alloc = FixedSizeAllocator::<8, 64>::new(false);

        for _ in 0..64 {
            assert!(alloc.as_mut().alloc::<usize>().is_some());
        }

        assert_eq!(alloc.total_free(), 0);
        assert_eq!(alloc.free_blocks(), 0);
    }


    #[test]
    fn check_free() {

        let mut alloc = FixedSizeAllocator::<8, 64>::new(false);

        let mut ptrs = Vec::with_capacity(64);
        for _ in 0..64 {
            ptrs.push(
                alloc.as_mut().alloc::<usize>().unwrap()
            );
        }

        for ptr in ptrs {
            if let Err(e) = alloc.as_mut().free_nonnull(ptr) {
                panic!("Unexpected error {:?}", e);
            }
        }

        assert_eq!(alloc.total_free(), alloc.heap_size());
        assert_eq!(alloc.free_blocks(), alloc.block_count());
    }


    #[test]
    fn check_new_stack() {

        let mut alloc = pin!( unsafe {
            FixedSizeAllocator::<8, 64>::new_unpinned_uninitialized(false)
        });
        unsafe {
            alloc.as_mut().init_bounds();
        }

        assert_eq!(alloc.block_size(), 8);
        assert_eq!(alloc.heap_size(), 64*8);
        assert_eq!(alloc.block_count(), 64);
        assert_eq!(alloc.free_blocks(), 64);
        assert_eq!(alloc.allocated_blocks(), 0);
        assert_eq!(alloc.total_allocated(), 0);
        assert_eq!(alloc.total_free(), alloc.heap_size());
    }


    #[test]
    fn check_alloc_stack() {

        let mut alloc = pin!( unsafe {
            FixedSizeAllocator::<8, 64>::new_unpinned_uninitialized(false)
        });
        unsafe {
            alloc.as_mut().init_bounds();
        }

        for _ in 0..64 {
            assert!(alloc.as_mut().alloc::<usize>().is_some());
        }

        assert_eq!(alloc.total_free(), 0);
        assert_eq!(alloc.free_blocks(), 0);
    }


    #[test]
    fn check_free_stack() {

        let mut alloc = pin!( unsafe {
            FixedSizeAllocator::<8, 64>::new_unpinned_uninitialized(false)
        });
        unsafe {
            alloc.as_mut().init_bounds();
        }
        
        let mut ptrs = Vec::with_capacity(64);
        for _ in 0..64 {
            ptrs.push(
                alloc.as_mut().alloc::<usize>().unwrap()
            );
        }

        for ptr in ptrs {
            if let Err(e) = alloc.as_mut().free_nonnull(ptr) {
                panic!("Unexpected error {:?}", e);
            }
        }

        assert_eq!(alloc.total_free(), alloc.heap_size());
        assert_eq!(alloc.free_blocks(), alloc.block_count());
    }


}

