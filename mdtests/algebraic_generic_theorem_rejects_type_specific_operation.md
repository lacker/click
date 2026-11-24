# a generic theorem is type-checked before any use

An unconstrained `T` supports parametric operations such as equality, not C
integer arithmetic.

```click
theorem invalid<T>(value: T) {
    ensures value + 1 == value by close();
}
```

```expect
fail: pure theorem `invalid`: an algebraic value is valid only as a comparison operand or match scrutinee
```
