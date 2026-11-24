# an induction hypothesis cannot be handed a wrapped range

`let ih = induct(n)` builds the hypothesis from the theorem's written `requires`,
so the span guards the theorem's own proof assumes are not among the
hypothesis's premises. That is only safe because of what it takes to satisfy a
range premise whose span wraps.

A range is viewable for free exactly when its span is decidably zero, and an
span is decidably zero only when its endpoints are decided — at which point
the shared definition decides the range invalid and the lowering keeps no path
for it. So the argument this proof would need, `ih(1073741824)`, cannot have its
range premise stated at all, and the theorem below is refused rather than
proved from a hypothesis stronger than itself.

The other direction is closed by arithmetic rather than by lowering: where the
range's endpoint is the induction variable, the theorem's own guards bound it,
and `0 <= x < n <= 1073741823` makes every smaller argument a valid span, so
the hypothesis is not stronger there.

```click
theorem a_cell_from_a_wrapped_hypothesis(v: int32[], n: int32) {
    requires 1073741825 <= n;
    requires n >= 0 and viewable(v[0..n]);
    ensures viewable(v[0..1]) by {
        let ih = induct(n);
        have 0 <= 1073741824;
        have 1073741824 < n by { close() using { 1073741825 <= n; }; }
        have viewable(v[0..1073741824]);
        have 1073741824 >= 0;
        have 1073741824 >= 0 and viewable(v[0..1073741824]) by close();
        apply(ih(1073741824));
        close();
    }
}
```

```expect
fail: a memory range is too wide to be a 32-bit byte span
```
