#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use std::ptr::NonNull;
use std::pin::Pin;
use std::mem::{self, MaybeUninit};
use std::marker::PhantomPinned;

use const_assert::{Assert, IsTrue};


/// Enum representing the pssible errors that may happen when freeing a pointer.
#[derive(Debug, Clone, Copy)]
pub enum FreeError {

    /// The freed pointer was a null pointer
    NullPtrFree,

    /// The freed pointer was already marked as free.
    DoubleFree,

    /// The freed pointer is outside the allocator's heap bounds.
    FreeOutOfBounds,

    /// The freed pointer is not aligned with any block's start address.
    UnalignedFree,

}


pub struct FixedSizeAllocator<const S: usize, const N: usize> {

    /// The heap
    memory: [MaybeUninit<[u8; S]>; N],

    /// Keep track of which blocks are free and which are allocated. A free block is `true` and an allocated block is `False`.
    free_table: [bool; N],

    /// The total amount of free memory in bytes.
    total_free: usize,

    /// A marker to tell the compiler that this struct must not be moved because it's in an address-sensitive state.
    _pin: PhantomPinned

}

impl<const S: usize, const N: usize> FixedSizeAllocator<S, N> 
where 
    Assert<{ S > 0 }>: IsTrue
{

    /// Construct a new fixed-size allocator on the stack and return it.
    /// Optionally, you can initialize the heap with `0` bytes by setting the `zero_initialized` flag. !This doesn't mean that the allocator is initialized!
    /// The returned allocator struct must immediately be pinned via `pin!()`. Using an unpinned allocator created on the stack is undefined behavior.
    /// This function is marked as unsafe because it's the programmer's responsibility to correctly instantiate and pin an allocator on the stack.
    pub unsafe fn new_unpinned(zero_initialized: bool) -> Self {

        let memory = if zero_initialized {
            [MaybeUninit::zeroed(); N]
        } else {
            [MaybeUninit::uninit(); N]
        };

        Self {
            memory,
            free_table: [true; N],
            total_free: S * N,
            _pin: Default::default()
        }
    }


    /// Return the start address of the heap.
    /// This coincides with the address of the first memory block.
    fn heap_start_address(&self) -> NonNull<u8> {
        unsafe {
            NonNull::new_unchecked(
                self.memory.as_ptr() as *mut u8
            )
        }   
    }


    /// Return the upper bound address of the heap.
    /// Note that this is an invalid pointer as it points to the first byte after the heap.
    fn upper_heap_bound(&self) -> NonNull<u8> {
        unsafe {
            self.heap_start_address().byte_add(S * N)
        }
    }


    /// Create a new fixed-size allocator on the heap using the standard system allocator.
    /// Optionally, you can initialize the heap with `0` bytes by setting the `zero_initialized` flag.
    /// Note that the returned allocator is pinned, meaning it cannot be moved once it's created. This is why a Pin<Box<>> is returned instead. 
    pub fn new(zero_initialized: bool) -> Pin<Box<Self>> {
        
        Box::pin( unsafe {
            Self::new_unpinned(zero_initialized)
        })
    }


    /// Return the total size of the heap in bytes.
    pub const fn heap_size(&self) -> usize {
        S * N
    }


    /// Return the total number of memory blocks.
    pub const fn block_count(&self) -> usize {
        N
    }


    /// Return the size of a memory block.
    pub const fn block_size(&self) -> usize {
        S
    }


    /// Return the total amount of free memory in bytes.
    pub const fn total_free(&self) -> usize {
        self.total_free
    }


    /// Return the total amount of memory allocated in bytes.
    pub const fn total_allocated(&self) -> usize {
        self.heap_size() - self.total_free()
    }


    /// Return how many blocks are free.
    pub fn free_blocks(&self) -> usize {
        self.free_table
            .iter()
            .filter(|&&is_free| is_free)
            .count()
    }


    /// Return how many blocks are allocated (not free).
    pub fn allocated_blocks(&self) -> usize {
        N - self.free_blocks()
    }


    pub unsafe fn alloc_untyped(self: Pin<&mut Self>) -> Option<NonNull<u8>> {

        let self_data = unsafe { self.get_unchecked_mut() };

        if self_data.total_free() == 0 {
            // Avoid searching for a free block if we already know we haven't got enough free memory
            None
        } else {
            // Binary search for a free block
            
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


    /// Try to allocate a memory block of that fits `T`, where `T` is `S`-sized.
    pub fn alloc<T>(self: Pin<&mut Self>) -> Option<NonNull<T>>
    where 
        Assert<{ mem::size_of::<T>() == S }>: IsTrue
    {
        unsafe {
            mem::transmute(self.alloc_untyped())
        }
    }


    /// Convert from a block's metadata index in the free table to the block's real address in memory.
    fn real_ptr_from_block_index<T>(&self, block_index: usize) -> NonNull<T> {

        // block address = heap start + (block index * block size)
        unsafe {
            NonNull::new_unchecked(
                self.heap_start_address().as_ptr().byte_add(block_index * self.block_size()) as *mut T
            )
        }
    }
    
    
    /// Convert from a block's real address in memory to its metadata entry index in the free table.
    /// Note that the given pointer must be aligned with the block's start address.
    fn block_index_from_real_ptr<T>(&self, ptr: NonNull<T>) -> Result<usize, FreeError> {

        // The pointer is invalid if it points outside of the heap.
        if (ptr.as_ptr() as usize) < (self.heap_start_address().as_ptr() as usize) || (ptr.as_ptr() as usize) >= (self.upper_heap_bound().as_ptr() as usize) {
            return Err(FreeError::FreeOutOfBounds)
        }

        // Calculate the positive offset from the heap start address.
        let offset = (ptr.as_ptr() as usize) - (self.heap_start_address().as_ptr() as usize);
           
        // Check for alignment
        if offset % self.block_size() != 0 {
            Err(FreeError::UnalignedFree)
        } else {
            Ok(
                // Calculate the actual block index
                offset / self.block_size()
            )
        }
    }


    /// Free the given non-null pointer.
    /// Note that the pointer must be aligned to the block's start address.
    pub fn free_nonnull<T>(self: Pin<&mut Self>, ptr: NonNull<T>) -> Result<(), FreeError> {

        let self_data = unsafe { self.get_unchecked_mut() };

        // Calculate the block's metadata index in the free table.
        let block_index = self_data.block_index_from_real_ptr(ptr)?;

        if self_data.free_table[block_index] {
            Err(FreeError::DoubleFree)
        } else {
            // Mark the block as free and keep track of the total free memory.
            self_data.free_table[block_index] = true;
            self_data.total_free += self_data.block_size();
            Ok(())
        }
    }


    /// Free the given pointer.
    /// Note that the pointer must be aligned to the block's start address.
    pub fn free<T>(self: Pin<&mut Self>, ptr: *const T) -> Result<(), FreeError> {

        if let Some(ptr) = NonNull::new(ptr as *mut T) {
            self.free_nonnull(ptr)
        } else {
            Err(FreeError::NullPtrFree)
        }
    }


    /// Free all the memory blocks.
    /// This function is inherently unsafe because it invalidates all pointers to previously allocated blocks.
    pub unsafe fn free_all(self: Pin<&mut Self>) {

        let self_data = unsafe { self.get_unchecked_mut() };

        // Simply mark all blocks as free
        self_data.free_table = [true; N];
        self_data.total_free = self_data.heap_size();
    }

}


#[cfg(test)]
mod tests {

    use std::{pin::pin, ptr};

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

        let alloc = pin!( unsafe {
            FixedSizeAllocator::<8, 64>::new_unpinned(false)
        });

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
            FixedSizeAllocator::<8, 64>::new_unpinned(false)
        });

        for _ in 0..64 {
            assert!(alloc.as_mut().alloc::<usize>().is_some());
        }

        assert_eq!(alloc.total_free(), 0);
        assert_eq!(alloc.free_blocks(), 0);
    }


    #[test]
    fn check_free_stack() {

        let mut alloc = pin!( unsafe {
            FixedSizeAllocator::<8, 64>::new_unpinned(false)
        });
        
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
    fn check_invalid_usage() {

        let mut alloc = FixedSizeAllocator::<{mem::size_of::<usize>()}, 64>::new(false);

        assert!(matches!(alloc.as_mut().free(ptr::null::<usize>()), Err(FreeError::NullPtrFree)));
        assert!(matches!(alloc.as_mut().free(1 as *const usize), Err(FreeError::FreeOutOfBounds)));
        assert!(matches!(alloc.as_mut().free(usize::MAX as *const usize), Err(FreeError::FreeOutOfBounds)));

        let ptr: NonNull<usize> = alloc.as_mut().alloc().unwrap();

        assert!(alloc.as_mut().free_nonnull(ptr).is_ok());
        assert!(matches!(alloc.as_mut().free_nonnull(ptr), Err(FreeError::DoubleFree)));
    }


    #[test]
    fn check_invalid_usage_stack() {

        let mut alloc = pin!( unsafe {
            FixedSizeAllocator::<{mem::size_of::<usize>()}, 64>::new_unpinned(false)
        });

        assert!(matches!(alloc.as_mut().free(ptr::null::<usize>()), Err(FreeError::NullPtrFree)));
        assert!(matches!(alloc.as_mut().free(1 as *const usize), Err(FreeError::FreeOutOfBounds)));
        assert!(matches!(alloc.as_mut().free(usize::MAX as *const usize), Err(FreeError::FreeOutOfBounds)));

        let ptr: NonNull<usize> = alloc.as_mut().alloc().unwrap();

        assert!(alloc.as_mut().free_nonnull(ptr).is_ok());
        assert!(matches!(alloc.as_mut().free_nonnull(ptr), Err(FreeError::DoubleFree)));
    }


    #[test]
    fn check_alloc_all_free_all() {

        let mut alloc = FixedSizeAllocator::<{mem::size_of::<u32>()}, 64>::new(false);

        for i in 0..64 {
            let ptr = alloc.as_mut().alloc::<u32>().unwrap();
            unsafe {
                ptr.write(i);
            }
        }

        assert_eq!(alloc.total_free(), 0);
        assert_eq!(alloc.total_allocated(), alloc.heap_size());
        assert_eq!(alloc.free_blocks(), 0);
        assert_eq!(alloc.allocated_blocks(), alloc.block_count());
        
        unsafe {
            alloc.as_mut().free_all();
        }

        assert_eq!(alloc.total_free(), alloc.heap_size());
        assert_eq!(alloc.free_blocks(), alloc.block_count());
        assert_eq!(alloc.allocated_blocks(), 0);
        assert_eq!(alloc.total_allocated(), 0);
    }


}

