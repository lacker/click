# a wrapped range cannot reach a `views` induction hypothesis

`mdtests/wrapped_range_cannot_reach_a_hypothesis.md` is this proof with the
range written as `requires n >= 0 and loadable(v[0..n]);`. A `views` clause
states the same range, so it owes the same thing at the same place: `induct(n)
as ih` recomputes the clause's byte-count guards at the substituted argument and
makes them premises of the hypothesis, and `apply(ih(1073741824))` owes the
range itself at that argument.

A range is loadable for free exactly when its extent is decidably zero, and an
extent is decidably zero only when its endpoints are decided — at which point
the shared definition decides the range invalid and the lowering keeps no path
for it. So the range premise `ih(1073741824)` needs cannot be stated at all, and
the theorem is refused rather than proved from a hypothesis stronger than
itself. `1073741824` four-byte elements is `1 << 32` bytes, which wraps to none.

```click
theorem a_cell_from_a_wrapped_views_hypothesis(v: int32[], n: int32) {
    views v[0..n];
    requires 1073741825 <= n;
    ensures loadable(v[0..1]) by {
        induct(n) as ih;
        have 0 <= 1073741824 by { simp(); }
        have 1073741824 < n by { simp() using { 1073741825 <= n; } }
        have loadable(v[0..1073741824]) by { simp(); }
        apply(ih(1073741824)) using {
            0 <= 1073741824;
            1073741824 < n;
            loadable(v[0..1073741824]);
        }
        assumption();
    }
}
```

```expect
fail: a memory range is too wide to be a 32-bit byte extent
```
