# Existential witnesses use let bindings

```click
theorem legacy_obtain() {
    requires exists (x: int32) { x == 0 };
    ensures true by {
        obtain (x: int32) { x == 0 }
        close();
    }
}
```

```expect
fail: write `let name = obtain(exists (k: Type) { P });`
```
