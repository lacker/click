# `defined` owes its operands' domains

`defined(a + b + c)` claims only the outer addition's domain. The inner
addition `a + b` is an operand, and nothing establishes its domain where the
requirement is stated, so the requirement is refused.

```click
theorem outer_only(a: int32, b: int32, c: int32) {
    requires defined(a + b + c);
    ensures 1 == 1 by close();
}
```

```expect
fail: not established: `a + b` must not overflow
```
