# An arbitrary type is not an empty inductive datatype

```click
theorem invalid<T>(x: T) {
    ensures 0 == 1 by { induct(x) as ih {} }
}
```

```expect
fail: invalid
```
