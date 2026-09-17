# `arithmetic using` proves int32 antisymmetry

Two opposite non-strict bounds over the same difference pin an equality. The
explicit tactic plans the kernel's `eq_from_bounds` step from exactly the two
listed premises.

```click
theorem antisym(a: int32, b: int32) {
    requires a <= b;
    requires b <= a;
    ensures a == b by {
        arithmetic() using {
            a <= b;
            b <= a;
        }
    }
}
```

```expect
pass
```
