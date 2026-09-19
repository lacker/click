# a loadable range too wide to be a byte extent is refused, not crashed

A `loadable` range becomes a physical byte extent: the base advances by
`start * width` and the extent is `(end - start) * width`, in the kernel's
32-bit memory model. Two side conditions have to hold before an element range
can be read that way — it must run forwards, and its scaled byte count must fit
in `u32` — and a range with constant endpoints is decided on the spot.

The decision used to compute `end - start` on the endpoints' `u32` bit
patterns. A negative start makes that subtraction underflow, which panicked the
verifier in a debug build and wrapped silently in a release one, where the
wrapped difference could look small enough to pass. The true difference is taken
in `i64` now, and the range is refused with what it came to.

```c filename=loadable_range_too_wide_for_a_byte_extent.c
int32 identity(int32 *p, int32 n) {
    return n;
}
```

```click
verifying "loadable_range_too_wide_for_a_byte_extent.c";

int32 identity(int32 *p, int32 n) {
    ensures result == n by {
        have loadable(p[-2000000000..2000000000]) by { simp(); }
        step();
        simp();
    }
}
```

```expect
fail: a memory range is too wide to be a 32-bit byte extent: 4000000000 elements of 4 bytes is 16000000000 bytes, past the 4294967295-byte limit
```
