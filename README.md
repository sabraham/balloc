# BALLOC
A Bad Allocator

## Why
To learn how allocators work

## How
C + GDB

## Allocation strategy
Free list is a BST with the address of the allocated blocks themselves being used as keys. Blocks have headers with left, right pointers to other Blocks, and a size_t size; allocated memory is sizeof(Block) + size.

## Is it any good?
Passable. Because the keys are the memory addresses, the BST leans heavily right, so performance degrades due to expensive search operations. Particularly, coalescing the successor is ~~prohibitively  expensive because the search operation for finding the successor is very expensive~~ relatively expensive (n log n). An immediate fix would be to implement the free tree as a balanced BST, additional simple buddy system would offer a large improvement.

## Who
Sunil Abraham and Martin Törnwall