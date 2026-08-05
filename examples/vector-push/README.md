# Vector Push

This focused project verifies a general in-capacity append. Starting from any
`0 <= len < cap`, `vector_push` writes exactly `data[old(len)]`, advances length
by one, preserves capacity and the backing pointer, and produces a nonempty
vector resource. Keeping this proof separate makes its performance independent
of the larger owned-vector pipeline.

Allocation and growth are separate concerns. Runtime allocation/free is in
`examples/runtime-int32-allocation`; malloc-copy-free vector growth remains
tracked in `issues/owned-vector-runtime-growth.md`.
