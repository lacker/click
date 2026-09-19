# a wrapped loadable extent must not yield a real cell

A witness, quarantined because it does not hold yet. It is not about range
narrowing: the narrowing rule refuses this shape, because it asks for the
assumed range's byte-count guards. The cell rules beside it do not, and this is
what that costs.

A `loadable` range becomes a byte extent `(end - start) * width`, in modular
32-bit arithmetic. At `n == 1 << 30` with four-byte elements that product is
`1 << 32`, which is `0`, so `loadable(v[0..n])` claims an empty extent and is
vacuously true — provable for any pointer, from nothing but the value of `n`.
The cell rules then read the same fact as "the elements `0..n`" and hand back
`v[0]`, four real bytes of an arbitrary pointer.

The byte-count guards exist to exclude exactly this, and on the proof side
nothing consults them: not a theorem's `requires`, not `apply(theorem(...))`,
not a `have`, not `extract`, not `transport`, not an induction hypothesis. They
are obligations only at a C call site, and a refusal on the composite-resource
unfold path.

Both halves below are separate theorems so the witness cannot be read as one
suspicious proof: the first shows the vacuous premise is free, the second turns
it into a cell.

```click
theorem a_wrapped_extent_is_free(v: int32[], n: int32) {
    requires n == 1073741824;
    ensures n >= 0 and loadable(v[0..n]) by {
        have n >= 0 by { arithmetic() using { n == 1073741824; } }
        have loadable(v[0..n]) by { simp(); }
        split();
    }
}

theorem a_wrapped_extent_yields_a_cell(v: int32[], n: int32) {
    requires n == 1073741824;
    requires n >= 0 and loadable(v[0..n]);
    ensures loadable(v[0..1]) by {
        have 0 <= 0 by { simp(); }
        have 0 <= 1 by { simp(); }
        have 1 <= n by { arithmetic() using { n == 1073741824; } }
        simp();
    }
}
```

```expect
fail: not a valid 32-bit byte extent
```
