# Runtime Int32 Allocation

This focused project verifies the supported runtime-sized heap slice without
mixing its resource definitions into a larger example. `allocate_int32s`
allocates `count * 4` bytes for a positive, signed-safe runtime count and
returns a conditional resource: null carries no allocation, while non-null owns
the exact allocation authority and `data[0..count]` memory. `free_int32s`
unfolds and consumes that complete resource. The same resource pair authorizes
a direct `free` inside a larger function: deallocation is tracked as a
heap-lifetime effect rather than requiring a fictitious mutable byte range or
an allocation-specific wrapper call.

This project remains the minimal allocation/free fixture. Its conditional
allocation resource is composed with copying, dependent pointer/capacity
replacement, and freeing the old allocation in the verified
[`examples/owned-vector`](../owned-vector/) growth operation. That integration
grows by exactly one slot (`new_cap = old_cap + 1`) rather than claiming a
general allocation or geometric-growth policy.

The current C0 boundary remains narrow: zero-sized allocation, arbitrary byte
layouts, `size_t`, `void *` conversions, custom allocators, `calloc`, and
`realloc` are not supported.
