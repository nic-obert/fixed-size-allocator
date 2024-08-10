use std::mem; 

use fixed_size_allocator::FixedSizeAllocator;



fn main() {

    const BLOCK_SIZE: usize = mem::size_of::<u32>();
    const BLOCK_COUNT: usize = 64;

    const INITIALIZE_WITH_ZEROS: bool = false;

    // Create an allocator that is placed on the standard system allocator's heap.
    let mut alloc = FixedSizeAllocator::<BLOCK_SIZE, BLOCK_COUNT>::new(INITIALIZE_WITH_ZEROS);

    // Allocate memory
    let ptr = alloc.as_mut().alloc::<u32>()
        .unwrap_or_else(|| panic!("Failed to allocate"));

    // Initialize the allocated memory
    unsafe {
        ptr.write(89);
        assert_eq!(ptr.read(), 89);
        *ptr.as_ptr() = 43;
        assert_eq!(*ptr.as_ptr(), 43);
    }

    // Finally, free the pointer
    alloc.as_mut().free_nonnull(ptr)
        .unwrap_or_else(|err| panic!("Failed to free pointer: {:?}", err));

}

