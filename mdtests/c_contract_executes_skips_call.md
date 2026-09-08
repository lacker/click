# Explicit callback execution: skips call

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* data) { owns data[0..1]; }
contract void Buffered(int32* data) { owns Buffer(data); }
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
 requires Raw(callback);
 ensures Buffered(callback) by { simp(); }
}
```

```expect
fail: execution
```
