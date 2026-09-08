# The target contract is an obligation, not a callback premise

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* p) { owns p[0..1]; }
contract void Buffered(int32* p) { owns Buffer(p); }
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Buffered(callback) by { step(Buffered); simp(); }
}
```

```expect
fail: is not established for this callback
```
