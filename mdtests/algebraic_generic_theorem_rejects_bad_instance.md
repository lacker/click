# a generic theorem proof is checked before use

An invalid generic proof grants no authority. Its declaration fails before a
concrete application can request it.

```click
theorem invalid<T>(left: T, right: T) {
    ensures left == right by simp;
}

theorem expose(left: int32, right: int32) {
    ensures left == right by {
        apply(invalid(left, right));
        assumption();
    }
}
```

```expect
fail: invalid.ensures_0
```
