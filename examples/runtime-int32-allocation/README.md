# Runtime Int32 Allocation

This focused project verifies the supported runtime-sized heap slice without
mixing its resource definitions into a larger example. `allocate_int32s`
allocates `count * 4` bytes for a positive, signed-safe runtime count and
returns a conditional resource: null carries no allocation, while non-null owns
the exact allocation authority and `data[0..count]` memory. `free_int32s`
unfolds and consumes that complete resource.

This is intentionally not vector growth. Copying between allocations, replacing
an owning object's dependent pointer/capacity resource, and freeing the old
allocation remain in `issues/owned-vector-runtime-growth.md` together with the
tooling and resource-model blockers that work exposed.

The current C0 boundary remains narrow: zero-sized allocation, arbitrary byte
layouts, `size_t`, `void *` conversions, custom allocators, `calloc`, and
`realloc` are not supported.
