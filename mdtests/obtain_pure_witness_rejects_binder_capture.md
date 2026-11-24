# An obtained witness does not capture a universal binder

```click
theorem bound_names(x: int32) {
    requires exists (k: int32) { k == x };
    ensures forall (k: int32) { k == x } by {
        let k = obtain(exists (k: int32) { k == x });
        intro();
        close();
    }
}
```

```expect
fail: could not establish `k == x`
```
