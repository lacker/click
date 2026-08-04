# Heap object

This project exercises one complete fixed-size allocation lifetime. `malloc`
returns either null or a fresh, uninitialized `struct item`. On success Click
tracks two independent resources: `object(item)` authorizes memory access,
while `allocation(item, sizeof(struct item))` is the exclusive authority and
obligation to end that allocation's lifetime.

`owned_item` packages those resources behind a conditional body. Its null case
is empty, so a factory can return one resource in both the allocation-failure
and success branches. `item_read` borrows a view of the object but receives no
authority to free it. `item_destroy` unfolds the owned resource and consumes
both complete access and allocation authority with `free`. Its Click proof
splits the nullable resource logically while leaving the branchless C
destructor unchanged: null is a no-op, and nonnull consumes the allocation.

`item_round_trip` shows the lifetime directly in one function.
`item_pipeline` checks that the same behavior survives modular factory,
borrower, and destructor calls.

New heap bytes are not zero-filled: every field is stored before it is read.
Allocation authority must be returned, transferred, or discharged by an
actual `free`; dropping a resource token does not count as deallocation.

This project intentionally stops at one object; the
[`allocated-linked-list`](../allocated-linked-list/) example composes the same
lifetime authority recursively. The supported heap slice still excludes
runtime-sized and zero-sized allocation, `calloc`, `realloc`, general `void *`
conversions, custom allocators, sharing, and concurrency.
