# Explicit callback execution: escaping argument

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* data) { owns data[0..1]; }
contract void Buffered(int32* data) { owns Buffer(data); }
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
 requires Raw(data);
 ensures Buffered(callback) by { step(Raw); }
}
```

```expect
fail: got an unknown type in requires clause
```
