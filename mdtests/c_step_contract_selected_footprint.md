# The selected contract supplies the owned footprint

Raw owns both cells; Buffered views the pair and owns only the first. Selecting
Buffered preserves the second cell through ownership alone.

```c filename=joint.c
void invoke(void (*callback)(int32*), int32* cells) { callback(cells); }
```

```click
resource Pair(cells: int32*) { owns cells[0..2]; }
contract void Raw(int32* cells) {
    owns cells[0..2];
}
contract void Buffered(int32* cells) {
    views Pair(cells);
    owns cells[0..1];
}
verifying "joint.c";
void invoke(void (*callback)(int32*), int32* cells) {
    requires Raw(callback);
    requires Buffered(callback);
    views Pair(cells);
    owns cells[0..1];
    ensures cells[1] == old(cells[1]);
} by { step(Buffered); execute(); simp(); }
```

```expect
pass
```
