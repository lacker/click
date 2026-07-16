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
indexed replacement, push, singleton pop, clear, and a pipeline of modular
calls. Indexed replacement demonstrates automatic frame transport for the
`terminated(data, len)` predicate: writing an earlier element preserves the
terminator fact and permits the proof to fold `owned_string(owner)` again
without manually re-proving the predicate. Push and pop move the terminator and
therefore establish the new predicate explicitly.

The caller supplies the backing storage. Allocation, deallocation, resizing,
and encoding validation are outside this example's scope.

One current proof-system boundary remains visible. Push and pop conservatively
declare the whole backing range mutable because precise field-derived effect
bases do not yet transport across the metadata write.
