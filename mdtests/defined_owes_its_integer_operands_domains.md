# `defined` owes its Integer operands' domains

`defined(to_int32(e))` claims only the conversion's range check. Its Integer
operand `to_integer(a / b)` is evaluated as an ordinary term, so the division's
domain is owed where the requirement is stated, and nothing establishes it.

```click
theorem integer_operand_owed(a: int32, b: int32) {
    requires defined(to_int32(to_integer(a / b)));
    ensures 1 == 1 by close();
}
```

```expect
fail: theorem `integer_operand_owed` setup failed: could not lower requirement
```
