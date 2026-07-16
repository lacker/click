# Owned String

This project verifies a sentinel-terminated string of integer code units whose
metadata and backing storage are packaged as one composite resource.

```c
struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};
```

The `owned_string(owner)` resource owns all three metadata fields and
`data[0..cap]`. Capacity counts allocated elements, so `len < cap` reserves one
element for the terminator. The resource records the content invariant
`terminated(data, len)`, whose definition is `data[len] == 0`. Keeping that
memory fact behind a one-step predicate makes observation finite while still
letting mutators unfold and re-establish the concrete terminator condition.

The verified operations cover initialization, viewed length and element reads,
push, singleton pop, clear, and a pipeline of modular calls. Push and pop move
the terminator while preserving the same composite resource.

The caller supplies the backing storage. Allocation, deallocation, resizing,
and encoding validation are outside this example's scope.

Two current proof-system boundaries remain visible. Push and pop conservatively
declare the whole backing range mutable because precise field-derived effect
bases do not yet transport across the metadata write. An indexed replacement
operation is omitted because preserving the snapshot-indexed `terminated` fact
across a provably disjoint symbolic store currently enters recursive alias
reasoning instead of framing the fact directly.
