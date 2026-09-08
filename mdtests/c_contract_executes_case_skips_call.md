# Every proof case must execute the callback

```click
resource Buffer(data: int32*, count: int32) { owns data[0..count]; }
contract void Raw(int32* p, int32 n) { requires n >= 0; owns p[0..n]; }
contract void Buffered(int32* p, int32 n) { requires n >= 0; owns Buffer(p, n); }
theorem lift(callback: void (*)(int32*, int32)) executes callback(int32* data, int32 count) {
    requires Raw(callback);
    ensures Buffered(callback) by {
        if count == 0 {
            simp();
        } else {
            unfold(Buffer(data, count)); step(Raw); fold(Buffer(data, count)); simp();
        }
    }
}
```

```expect
fail: execution
```
