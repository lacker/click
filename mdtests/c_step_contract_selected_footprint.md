# The selected contract supplies the mutable footprint

Raw permits mutation of both cells; Buffered permits only the first. Selecting
Buffered preserves the second cell through the ordinary frame machinery.

```c filename=joint.c
void invoke(void (*callback)(int32*), int32* cells) { callback(cells); }
```

```click
resource Pair(cells: int32*) { owns cells[0..2]; }
contract void Raw(int32* cells) {
    owns cells[0..2];
    mutable cells[0..2];
}
contract void Buffered(int32* cells) {
    owns Pair(cells);
    mutable cells[0..1];
}
verifying "joint.c";
void invoke(void (*callback)(int32*), int32* cells) {
    requires Raw(callback);
    requires Buffered(callback);
    owns Pair(cells);
    mutable cells[0..1];
    ensures cells[1] == old(cells[1]);
} by { step(Buffered); execute(); frame(); simp(); }
```

```expect
pass
```
