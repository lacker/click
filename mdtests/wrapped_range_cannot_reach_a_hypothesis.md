# an induction hypothesis cannot be handed a wrapped range

`induct(n) as ih` builds the hypothesis from the theorem's written `requires`,
so the extent guards the theorem's own proof assumes are not among the
hypothesis's premises. That is only safe because of what it takes to satisfy a
range premise whose extent wraps.

A range is loadable for free exactly when its extent is decidably zero, and an
extent is decidably zero only when its endpoints are decided — at which point
the shared definition decides the range invalid and the lowering keeps no path
for it. So the argument this proof would need, `ih(1073741824)`, cannot have its
range premise stated at all, and the theorem below is refused rather than
proved from a hypothesis stronger than itself.

The other direction is closed by arithmetic rather than by lowering: where the
range's endpoint is the induction variable, the theorem's own guards bound it,
and `0 <= x < n <= 1073741823` makes every smaller argument a valid extent, so
the hypothesis is not stronger there.

```click
theorem a_cell_from_a_wrapped_hypothesis(v: int32[], n: int32) {
    requires 1073741825 <= n;
    requires n >= 0 and loadable(v[0..n]);
    ensures loadable(v[0..1]) by {
        induct(n) as ih;
        have 0 <= 1073741824 by { simp(); }
        have 1073741824 < n by { simp() using { 1073741825 <= n; } }
        have loadable(v[0..1073741824]) by { simp(); }
        have 1073741824 >= 0 by { simp(); }
        have 1073741824 >= 0 and loadable(v[0..1073741824]) by { split(); }
        apply(ih(1073741824)) using {
            0 <= 1073741824;
            1073741824 < n;
            1073741824 >= 0 and loadable(v[0..1073741824]);
        }
        assumption();
    }
}
```

```expect
fail: a memory range is too wide to be a 32-bit byte extent
```
