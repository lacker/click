# A returned status selects the callback's state guarantee

The callback makes no promise that it succeeds. Both the refinement proof and
an ordinary C caller must use its status before relying on either guarantee.

```c filename=status.c
int32 check_update(int32 (*callback)(int32*, int32), int32* cell, int32 value) {
    int32 before = *cell;
    int32 status = callback(cell, value);
    if (status != 0) {
        return *cell == value;
    } else {
        return *cell == before;
    }
}
```

```click
resource Cell(p: int32*) { owns p[0..1]; }
contract int32 Raw(int32* p, int32 value) {
    owns p[0..1]; mutable p[0..1];
    ensures result == 0 or result == 1;
    ensures result != 0 implies p[0] == value;
    ensures result == 0 implies p[0] == old(p[0]);
}
contract int32 Buffered(int32* p, int32 value) {
    owns Cell(p); mutable p[0..1];
    ensures result == 0 or result == 1;
    ensures result != 0 implies p[0] == value;
    ensures result == 0 implies p[0] == old(p[0]);
}
theorem lift(callback: int32 (*)(int32*, int32))
    executes callback(int32* cell, int32 item)
{
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Cell(cell));
        step(Raw);
        if result != 0 {
            have cell[0] == item by { extract(cell[0] == item); assumption(); }
            fold(Cell(cell)); frame(); simp();
        } else {
            have cell[0] == old(cell[0]) by {
                extract(cell[0] == old(cell[0])); assumption();
            }
            fold(Cell(cell)); frame(); simp();
        }
    }
}
verifying "status.c";
int32 check_update(int32 (*callback)(int32*, int32), int32* cell, int32 value) {
    requires Raw(callback);
    owns Cell(cell); mutable cell[0..1];
    ensures result == 1;
} by {
    apply(lift(callback));
    unfold(Cell(cell));
    step(); step(); step();
    fold(Cell(cell));
    step(Buffered);
    unfold(Cell(cell));
    if c(status) != 0 {
        have cell[0] == value by { extract(cell[0] == value); assumption(); }
        execute(); fold(Cell(cell)); frame(); simp();
    } else {
        have cell[0] == c(before) by { simp(); }
        execute(); fold(Cell(cell)); frame(); simp();
    }
}
```

```expect
pass
```
