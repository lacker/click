# Allocated Linked List

This project combines the fixed-size heap model with a guarded recursive
resource. A nonnull `allocated_list(node)` owns the node's complete object,
the exclusive authority to free its allocation, and the recursively folded
tail. The null list owns nothing.

`list_prepend` consumes a tail and returns one list in both allocator outcomes.
If allocation fails it returns the original tail unchanged. On success it
initializes a fresh node and folds that node around the tail. The proof splits
on `result == tail`, which distinguishes reuse from fresh allocation without
requiring the C implementation to expose proof-oriented control flow.

`list_head` borrows the recursive resource. `list_drop_front` unfolds and frees
exactly one node, returning ownership of the still-live tail. `list_destroy`
is an ordinary `void` postorder destructor: its null arm is empty, while its
nonnull arm passes the direct contained tail to a standalone recursive call
and then frees the parent. `decreases resource allocated_list(node)` proves
termination from that finite ownership witness even though the function
consumes and deallocates it. Its `if (!node)` spelling also demonstrates that
termination uses the meaning of a guard rather than requiring one exact syntax.

The pipeline makes two independent allocation attempts, borrows the resulting
head when present, drops one node, and destroys the remainder through verified
modular contracts. Allocation failure at either prepend remains safe and
leak-free.

The example intentionally excludes shared tails, cycles, runtime-sized nodes,
custom allocators, and concurrent access.
