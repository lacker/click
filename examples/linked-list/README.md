# Preallocated Linked List

This example models an arbitrary finite singly linked list with a guarded,
recursive composite resource. A null head has an empty body. A nonnull head
owns its two fields and contains the still-folded resource for its successor.

Nodes are supplied by the caller. `list_empty` returns C's null pointer
constant. `list_push_front` transfers a detached node and an existing list into
a new list. `list_pop_front` performs the reverse ownership transfer while
leaving the old `next` value in the detached node. Explicit `fold` and `unfold`
operations expose exactly one node; the kernel does not recursively expand the
tail.

The project intentionally does not cover allocation, deallocation, traversal
loops, shared tails, or cyclic lists.
