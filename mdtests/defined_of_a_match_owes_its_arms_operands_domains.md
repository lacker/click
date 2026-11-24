# `defined` of a `match` owes its arms' operands' domains

An arm's body claims its own root with its operands as values, so the inner
addition `a + b` is owed where its arm is taken, and nothing establishes it.

```click
spec enum Step {
    Next(int32),
    Stay(int32),
}

theorem arm_operand_owed(s: Step, a: int32, b: int32) {
    requires defined(match s {
        Step::Next(x) => x + (a + b),
        Step::Stay(x) => x,
    });
    ensures 1 == 1 by close();
}
```

```expect
fail: theorem `arm_operand_owed` setup failed: could not lower requirement
```
