# The execution header cannot silently bind a different callback

```click
contract void Raw(int32* data) { owns data[0..1]; }
contract void Buffered(int32* data) { owns data[0..1]; }
theorem lift(callback: void (*)(int32*)) executes other(int32* data) {
    requires Raw(callback);
    ensures Buffered(callback) by { step(Raw); simp(); }
}
```

```expect
fail: the executed callback must be the theorem's function-pointer parameter
```
