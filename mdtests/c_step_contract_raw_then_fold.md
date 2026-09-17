# Select raw ownership, then fold it explicitly

The selected contract returns the raw model; ordinary folding restores the caller's composite resource.

```c filename=joint.c
int32 invoke(void (*callback)(int32*, int32), int32* data, int32 count) {
    callback(data, count);
    return 0;
}
```

```click
resource Buffer(data: int32*, count: int32) { owns data[0..count]; }
contract void Raw(int32* data, int32 count) {
    requires count >= 0;
    owns data[0..count];
}
contract void Buffered(int32* data, int32 count) {
    requires count >= 0;
    owns Buffer(data, count);
}
verifying "joint.c";
int32 invoke(void (*callback)(int32*, int32), int32* data, int32 count) {
    requires Raw(callback);
    requires Buffered(callback);
    requires count >= 0;
    owns Buffer(data, count);
    ensures result == 0;
} by { step(Raw); fold(Buffer(data, count)); execute(); simp(); }
```

```expect
pass
```
