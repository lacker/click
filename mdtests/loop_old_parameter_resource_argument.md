# Loop resources retain entry-bound parameters when the C cursor changes

The loop keeps the cell at the function-entry pointer while `rb` advances.
Rebinding must capture `old(rb)` and must still evaluate current arguments in
current state. The scalar case checks the same rule without pointer conversion.

```c filename=advance.c
void advance(int32 *rb, int32 *stop) {
    while (rb != stop) {
        rb = stop;
    }
}
void change_index(int32 *p, int32 index) {
    while (index > 0) {
        index = 0;
    }
}
```
```click
verifying "advance.c";
resource Cell(p: int32*) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
}
resource IndexedCell(p: int32*, index: int32) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
}
function remaining(rb: int32*, stop: int32*) -> int32 {
    if address(rb) == address(stop) { 0 } else { 1 }
}
void advance(int32* rb, int32* stop) {
    owns cell: Cell(rb);
    ensures cell.value == old(cell.value);
} by {
    loop {
        decreases remaining(rb, stop);
        owns cell: Cell(old(rb));
        invariant cell.value == old(cell.value);
        initialize by close();
        maintain by {
            have remaining(rb, stop) == 1 by {
                unfold(remaining(rb, stop));
                close() using { address(rb) != address(stop); };
            }
            step();
            have remaining(rb, stop) == 0 by {
                unfold(remaining(rb, stop));
                close() using { address(rb) == address(stop); };
            }
        }
    }
}
void change_index(int32* p, int32 index) {
    requires index >= 0;
    owns cell: IndexedCell(p, index);
    ensures cell.value == old(cell.value);
} by {
    loop {
        decreases index;
        owns cell: IndexedCell(p, old(index));
        invariant index >= 0;
        invariant cell.value == old(cell.value);
        initialize by close();
        maintain by { step(); }
    }
}
```
```expect
pass
```
