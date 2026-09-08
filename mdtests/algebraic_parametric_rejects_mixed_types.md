# Distinct arbitrary types are not interchangeable

```click
theorem invalid<T, U>(x: T, y: U) {
    ensures x == y by { normalize(); }
}
```

```expect
fail: invalid
```
