# a range below the owner is not part of it

An element index is signed. `p[-1..0]` is the element *before* `p`, exactly as
`p[1..2]` is the element after it, and a caller holding `p[0..1]` holds neither
of them.

`memory_range_covers`' constant-arithmetic arm read both endpoints of both
ranges through `Bitvector32Term::as_const`, which answers `u32`. So `-1`
arrived as `4294967295`, which clears `available_start <= required_start`
against every owner there is, while the requirement's own end — `0` — cleared
the other side against every owner whose end is nonnegative. `owns p[0..1]`
therefore entailed `owns p[-1..0]`, and the caller below could hand the element
below its array to a callee that writes it:

    int32 write_first(int32* r, int32 start, int32 end, int32 value) {
        r[start] = value;            //  consumes r[start..end]
        return value;
    }

    int32 below_the_range(int32* p) {        //  consumes p[0..1]
        return write_first(p, -1, 0, 7);     //  writes p[-1]
    }

`below_the_range` owns one element, `p[0]`, and the call writes `p[-1]`. It
verified.

Containment is a statement about addresses, so it is now decided in `i64` from
each range's *start* and *count* — the count being the signed value of the
32-bit term `end - start`, which is what `memory_range_byte_count` scales — and
from a base delta `Pointer::exact_element_delta_from_base` gives exactly.
`a_range_below_the_owner_is_not_covered_by_it` and its two neighbours in
`kernel::tests::resource_tests::constant_range_containment` pin the arithmetic
at the boundary, including the base `i32::MIN` elements below an owner whose
relative endpoints wrap back into it.

`writes_its_own_first_element` is the positive next door: the same call at the
element the caller does own.

```c filename=a_range_below_the_owner_is_not_owned.c
int32 write_first(int32* r, int32 start, int32 end, int32 value) {
    r[start] = value;
    return value;
}

int32 below_the_range(int32* p) {
    return write_first(p, -1, 0, 7);
}

int32 writes_its_own_first_element(int32* p) {
    return write_first(p, 0, 1, 7);
}
```

```click
verifying "a_range_below_the_owner_is_not_owned.c";

int32 write_first(int32* r, int32 start, int32 end, int32 value) {
    requires start < end;
    consumes r[start..end];
    ensures result == value;
} by {
    execute();
    simp();
}

int32 writes_its_own_first_element(int32* p) {
    consumes p[0..1];
    ensures result == 7;
} by {
    execute();
    simp();
}

int32 below_the_range(int32* p) {
    consumes p[0..1];
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns p[-1..0]`
```
