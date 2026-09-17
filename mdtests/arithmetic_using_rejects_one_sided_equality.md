# `arithmetic using` still needs both bounds for an equality

One bound does not pin an equality. The planner closes an equality goal only
when both opposite bounds come from the listed premises, so listing just the
one available half fails locally rather than reaching into the context for the
other one.

```click
theorem antisym_one_bound(a: int32, b: int32) {
    requires a <= b;
    requires b <= a;
    ensures a == b by {
        arithmetic() using {
            a <= b;
        }
    }
}
```

```expect
fail: current goal does not follow from exactly the listed arithmetic premises
```
