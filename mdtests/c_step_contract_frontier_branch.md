# Select a callback transition inside a C branch

```c filename=joint.c
void invoke(void (*callback)(int32*), int32* cell, int32 active) {
    if (active) { callback(cell); } else { callback(cell); }
}
```

```click
resource Cell(cell: int32*) { owns cell[0..1]; }
contract void Raw(int32* cell) { owns cell[0..1]; }
contract void Buffered(int32* cell) { owns Cell(cell); }
verifying "joint.c";
void invoke(void (*callback)(int32*), int32* cell, int32 active) {
    requires Raw(callback);
    requires Buffered(callback);
    owns Cell(cell);
} by {
    branch {
        then { step(Buffered); }
        else { step(Buffered); }
    }
    execute();
    simp();
}
```

```expect
pass
```
