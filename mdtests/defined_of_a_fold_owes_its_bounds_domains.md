# `defined` of a fold owes its bounds' domains

A range fold's root is the fold itself, including every pass of its body. Its
bounds and initial value are operands: `a + b` is owed where the requirement
is stated, and nothing establishes it.

```click
theorem fold_bound_owed(a: int32, b: int32) {
    requires defined((0..(a + b)).fold(0, |acc, k| { acc | k }));
    ensures 1 == 1 by close();
}
```

```expect
fail: theorem `fold_bound_owed` setup failed: could not lower requirement
```
