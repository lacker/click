# Owned String

This project verifies a length-tracked string of integer code units with a
trailing zero terminator. Its metadata and backing storage are packaged as one
composite resource.

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
`terminated_at(data, len)`, whose definition is `data[len] == 0`. This does not
prohibit zero values before `len`; it states exactly where the trailing
terminator is maintained. Keeping that memory fact behind a one-step predicate
makes observation finite while still letting mutators unfold and re-establish
the concrete terminator condition.

The verified operations cover initialization, viewed length and element reads,
indexed replacement, push, general pop, clear, and a pipeline of modular calls.
Indexed replacement explicitly unfolds and re-establishes the terminator
predicate after its separate store. Push and pop move the terminator and
therefore establish the new predicate explicitly.

Push declares only the metadata length and the two cells beginning at the old
end as mutable. Its field-derived backing pointer remains identifiable after
the metadata write. `owned_string_push_preserves_first` calls push through its
verified contract and proves that an earlier cell is unchanged, demonstrating
that the precise footprint is useful to modular callers. Its contract-level
`data` binding captures the entry backing pointer without adding a proof-only C
parameter. Pop similarly mutates only the metadata length and the old final
content cell. `owned_string_pop_preserves_first` verifies through that modular
contract that popping a string of length at least two preserves its first
element.

The caller supplies the backing storage. Allocation, deallocation, resizing,
and encoding validation are outside this example's scope.
