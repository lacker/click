# a generic theorem proof is checked before use

An invalid generic proof grants no authority. The error is reported when a
concrete application first requests that monomorph.

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
fail: generic theorem instance `invalid::<int32>` failed verification
```
