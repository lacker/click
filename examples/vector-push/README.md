# Vector Push

This focused project verifies a general in-capacity append. Starting from any
`0 <= len < cap`, `vector_push` writes exactly `data[old(len)]`, advances length
by one, preserves capacity and the backing pointer, and produces a nonempty
vector resource. Keeping this proof separate makes its performance independent
of the larger owned-vector pipeline.

This project deliberately isolates the in-capacity operation so it can be
profiled independently. [`examples/owned-vector`](../owned-vector/) composes
runtime allocation, copying, pointer/capacity replacement, and freeing the old
allocation into verified malloc-copy-free growth. That integration uses the
focused `old_cap + 1` policy; it is not a geometric-growth or `realloc`
example. The minimal allocation/free fixture remains in
[`examples/runtime-int32-allocation`](../runtime-int32-allocation/).
