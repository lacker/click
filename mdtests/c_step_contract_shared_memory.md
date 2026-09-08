# Other applicable memory guarantees use the selected call's post-state

```c filename=joint.c
int32 invoke(int32 (*callback)(int32*), int32* cell) { return callback(cell); }
```

```click
resource Cell(cell: int32*) { owns cell[0..1]; }
contract int32 Raw(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
    ensures cell[0] == 7;
}
contract int32 Buffered(int32* cell) {
    owns Cell(cell);
    mutable cell[0..1];
    ensures result == cell[0];
}
verifying "joint.c";
int32 invoke(int32 (*callback)(int32*), int32* cell) {
    requires Raw(callback);
    requires Buffered(callback);
    owns Cell(cell);
    mutable cell[0..1];
    ensures result == 7;
    ensures cell[0] == 7;
} by { step(Buffered); execute(); frame(); simp(); }
```

```expect
pass
```
