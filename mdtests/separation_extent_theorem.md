# Separation theorem premises carry the same bounds their applications owe

```click
theorem nonnegative(a: int32[], b: int32[], n: int32) {
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures 0 <= n by { assumption(); }
}

theorem bounded_application(a: int32[], b: int32[], n: int32) {
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures 0 <= n by {
        apply(nonnegative(a, b, n)) using {
            separate(memory(a[0..n]), memory(b[0..1]));
        }
    }
}
```

```expect
pass
```
