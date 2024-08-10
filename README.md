# Fixed size allocator

A fixed size allocator implemented in Rust

- [Fixed size allocator](#fixed-size-allocator)
- [Basic usage](#basic-usage)
- [How it works](#how-it-works)
  - [Allocator initialization](#allocator-initialization)
  - [Allocating and deallocating memory](#allocating-and-deallocating-memory)
  - [Converting from block address to free table index and vice versa](#converting-from-block-address-to-free-table-index-and-vice-versa)
- [License](#license)

# Basic usage


Create and use the allocator:

```rust
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

```


Create the allocator on the stack. The allocator must be instantiated on the stack if the standard system allocator is not available or you don't want to use it.

```rust
const BLOCK_SIZE: usize = mem::size_of::<u32>();
const BLOCK_COUNT: usize = 64;

const INITIALIZE_WITH_ZEROS: bool = false;

// Create an allocator on the stack and pin it in place.
// Pinning is required to use the allocator safely.
let mut alloc = pin!( unsafe {
    FixedSizeAllocator::<BLOCK_SIZE, BLOCK_COUNT>::new_unpinned(INITIALIZE_WITH_ZEROS)
});

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
```

# How it works

## Allocator initialization

A fixed-size allocator works by pre-allocating a chunk of memory that can fit an arbitrary number of `N` memory blocks, each of which is `S` bytes large, where `S` is a positive non-zero integer and `N` is a positive integer. The total heap size is then `S * N`. The heap is equivalent to an array of the form `[[u8; S]; N]`.  

The heap is then logically split into `N` blocks of `S` bytes and a free table is used to keep track of which blocks are free and which are allocated. The free table is implemented as an array of `N` boolean values (`[bool; N]`), each of which represents the state of its associated memory block: `true` means the block is free, while `false` means the block is allocated.  

## Allocating and deallocating memory

Upon an allocation request, the allocator searches through the free table using a binary search algorithm and, if a free block is found, it marks the block as allocated and returns the pointer to the start of the newly allocated block.

Upon a free request, the allocator calculates the index of the block's metadata in the free table from the given pointer. The block is then marked as free in the free table.

## Converting from block address to free table index and vice versa

Since the heap is pinned in memory, its memory address cannot change. This means that pointers to blocks allocated on the heap remain valid for the lifetime of the allocator.

The free table stores the memory block metadata in increasing address order. The offset from the start of the heap is then proportional to the block's index in the free table so that `offset = index * block size`. The real address of the memory block is then calculated by offsetting the start of the heap by the calculated offset: `block address = heap address + (block index * block size)`.

A block's metadata index in the free table is then calculated by reversing the aforementioned algorithm: `block index = (block address - heap address) / block size`.


# License

This respository and all files within it are published under the [MIT license](LICENSE).
