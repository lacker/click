# Only one applicable interface may carry the resource transition

The inapplicable pure interface does not prevent the ordinary resource-backed
call, and its stronger guarantee is not needed.

```c filename=joint.c
int32 invoke(int32 (*callback)(int32*, int32), int32* cell, int32 x) {
    return callback(cell, x);
}
```

```click
contract int32 Positive(int32* cell, int32 value) {
    requires value > 0;
    ensures result == 1;
}
contract int32 Read(int32* cell, int32 value) {
    owns cell[0..1];
    ensures result == cell[0];
}
verifying "joint.c";
int32 invoke(int32 (*callback)(int32*, int32), int32* cell, int32 x) {
    requires Positive(callback);
    requires Read(callback);
    requires x == 0;
    owns cell[0..1];
    ensures result == cell[0];
} by { execute(); simp(); }
```

```expect
pass
```
