# Explicit callback execution: collision

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* data) { owns data[0..1]; }
contract void Buffered(int32* data) { owns Buffer(data); }
theorem lift(callback: void (*)(int32*)) executes callback(int32* callback) {
 requires Raw(callback);
 ensures Buffered(callback) by { step(Raw); }
}
```

```expect
fail: call argument names must be distinct
```
