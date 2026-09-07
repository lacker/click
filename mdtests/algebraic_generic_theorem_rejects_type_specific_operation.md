# a generic theorem is type-checked before any use

An unconstrained `T` supports parametric operations such as equality, not C
integer arithmetic.

```click
theorem invalid<T>(value: T) {
    ensures value + 1 == value by simp;
}
```

```expect
fail: C operator cannot be applied to a generic or algebraic value in theorem `invalid` ensure
```
