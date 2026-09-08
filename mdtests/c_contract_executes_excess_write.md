# The public contract's write footprint remains an obligation

```click
resource Buffer(data: int32*) { owns data[0..2]; }
contract void Raw(int32* data) { owns data[0..2]; mutable data[0..2]; }
contract void Buffered(int32* data) { owns Buffer(data); mutable data[0..1]; }
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data)); step(Raw); fold(Buffer(data)); frame(); simp();
    }
}
```

```expect
fail: is outside the mutable footprint
```
