# A signed upper bound alone does not bound an unsigned range

Negative signed lengths become large unsigned values. The byte bound must not
follow without a nonnegative lower bound.

```click
theorem missing_lower_bound(length: int32) {
    requires length <= 536870911;
    ensures ((uint32)length) <= 1073741823u32 by {
        arithmetic() using {
            length <= 536870911;
        }
    }
}
```

```expect
fail: does not follow from exactly the listed arithmetic premises
```
