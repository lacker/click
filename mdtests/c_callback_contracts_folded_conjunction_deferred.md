# Folded resource conjunction remains explicitly deferred

Both behavioral facts may be known after refinement. Ordinary resource matching
can use the folded resource for either interface. Combining those alternative
owned descriptions remains explicitly deferred, rather than selecting a view
by contract-name order or returning two successors.

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
} by { execute(); simp(); }
```

```expect
fail: combining resource-bearing callback contracts is not yet supported
```
