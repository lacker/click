# Return values can relate entry memory to the new contents

```click
resource Cell(p: int32*) { owns p[0..1]; }
contract int32 Exchange(int32* p, int32 value) {
    owns p[0..1]; mutable p[0..1];
    ensures result == old(p[0]);
    ensures p[0] == value;
}
contract int32 Buffered(int32* p, int32 value) {
    owns Cell(p); mutable p[0..1];
    ensures result == old(p[0]);
    ensures p[0] == value;
}
theorem lift(callback: int32 (*)(int32*, int32)) executes callback(int32* cell, int32 item) {
    requires Exchange(callback);
    ensures Buffered(callback) by {
        unfold(Cell(cell)); step(Exchange);
        have result == old(cell[0]) by { assumption(); }
        have cell[0] == item by { assumption(); }
        fold(Cell(cell)); frame(); simp();
    }
}
```

```expect
pass
```
