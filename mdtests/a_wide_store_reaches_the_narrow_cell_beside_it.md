# a wide store is not framed away from the narrow cell it covers

A store drops every cell of its own block whose bytes it may have written,
and keeps the rest. Two questions decide which: `StoreByteInterval::overwrites`
asks about bytes, and an address-separation ladder asks about addresses.

`overwrites` answers only where the two offsets carry the same symbolic atoms
— it is the constant-gap test, and it declines a cell at `a[i]` against a
store at `a[j]`. So for exactly the pairs it could not decide, the ladder was
deciding the byte question alone, and an address is not that question:
`i != j` separates `a[i]` from `a[j]` and says nothing about an eight-byte
store there, which covers `a[j]` and `a[j + 1]` both.

    int32_t upper_half_survives(int32_t* a, int32_t i, int32_t j) {
        int64_t* w;
        a[i] = 5;
        w = (int64_t*)(void*) &a[j];
        *w = 0;
        return a[i];              //  proved  result == 5
    }

Under `0 <= j < 3`, `0 <= i < 4` and `i != j` that verified, and `j == 0`,
`i == 1` satisfies every one of those premises while the store writes `a[1]`.
The refusal that asked for `i != j` was the invitation: stating the premise
the diagnostic named was what turned the ladder on.

The ladder is now conjoined with the shared `access_byte_overlap`, exactly as
`step_effect::cell_effect` and the snapshot comparisons conjoin it: the
ladder decides whether the addresses differ, and the byte answer decides
whether the gap it establishes clears both accesses. An unknown gap blocks it
too. Both widths are exact at this site — the store's is its own, the cell's
is the width of the value it holds — which is why it can be asked here at
all.

`access_byte_overlap` also declined a pair with no additive base to cancel,
`a + 4` against `a[i]`, which is the shape the kernel's own
`symbolic_store_invalidates_only_possible_aliasing_cells` is written in.
Their own offsets are the indices there, and reading them is sound for the
same reason a cancelled pair's are: `element_index_from_offset` answers only
where every leaf contributes a whole multiple of the element width, and two
different multiples of `w` are at least `w` apart.

`narrow_store_leaves_the_distinct_element` is the positive next door: the
same two indices and the same disequality, with a four-byte store that really
does miss the cell.

The two range rungs beside the ladder — `pointers_directly_disjoint_by_range`
and `owned_composition_store_separated_evidence` — place an access by its
first element and are not gated here. Gating them costs seventeen proofs
across `examples/`, because `access_byte_overlap` has no cross-base rung and
answers `Unknown` for every pair they exist to decide.

```c filename=a_wide_store_reaches_the_narrow_cell_beside_it.c
#include <stdint.h>

int32_t narrow_store_leaves_the_distinct_element(int32_t* a, int32_t i, int32_t j) {
    a[i] = 5;
    a[j] = 0;
    return a[i];
}

int32_t upper_half_survives(int32_t* a, int32_t i, int32_t j) {
    int64_t* w;
    a[i] = 5;
    w = (int64_t*)(void*) &a[j];
    *w = 0;
    return a[i];
}
```

```click
verifying "a_wide_store_reaches_the_narrow_cell_beside_it.c";

int32_t narrow_store_leaves_the_distinct_element(int32_t* a, int32_t i, int32_t j) {
    requires 0 <= j;
    requires j < 3;
    requires 0 <= i;
    requires i < 4;
    requires i != j;
    owns a[0..4];
    ensures result == 5;
} by {
    execute();
    simp();
}

int32_t upper_half_survives(int32_t* a, int32_t i, int32_t j) {
    requires 0 <= j;
    requires j < 3;
    requires 0 <= i;
    requires i < 4;
    requires i != j;
    owns a[0..4];
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: result == 5
```
