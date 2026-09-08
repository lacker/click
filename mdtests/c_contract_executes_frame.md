# Explicit callback execution: frame

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* data, int32* spare) { owns data[0..1]; }
contract void Buffered(int32* data, int32* spare) { owns Buffer(data); owns Buffer(spare); }
theorem lift(callback: void (*)(int32*, int32*)) executes callback(int32* p, int32* q) {
 requires Raw(callback);
 ensures Buffered(callback) by { unfold(Buffer(p)); step(Raw); fold(Buffer(p)); simp(); }
}
```

```expect
pass
```
