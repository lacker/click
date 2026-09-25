# Pure theorems cannot assert path-local mutex ownership

```click
theorem always_unheld(m: int32*) {
    ensures not held(m) by { simp(); }
}
```

```expect
fail: held
```
