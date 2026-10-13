# `auto` refuses an addition that may overflow

With `total` bounded only by `int32` itself, `total + 1` may overflow, so
`defined(total + 1)` does not follow.

```click
theorem may_overflow(total: int32) {
    requires 0 <= total;
    ensures defined(total + 1) by {
        have defined(total + 1) by auto;
        assumption();
    }
}
```

```expect
fail: could not complete tactic 1 (`have`)
```
