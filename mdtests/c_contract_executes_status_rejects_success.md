# Failure must not inherit the success guarantee

```click
resource Cell(p: int32*) { owns p[0..1]; }
contract int32 Raw(int32* p, int32 value) {
    owns p[0..1]; mutable p[0..1];
    ensures result == 0 or result == 1;
    ensures result != 0 implies p[0] == value;
    ensures result == 0 implies p[0] == old(p[0]);
}
contract int32 AlwaysSets(int32* p, int32 value) {
    owns Cell(p); mutable p[0..1];
    ensures p[0] == value;
}
theorem unsound(callback: int32 (*)(int32*, int32))
    executes callback(int32* cell, int32 item)
{
    requires Raw(callback);
    ensures AlwaysSets(callback) by {
        unfold(Cell(cell)); step(Raw);
        if result != 0 {
            fold(Cell(cell)); frame(); simp();
        } else {
            fold(Cell(cell)); frame(); simp();
        }
    }
}
```

```expect
fail: simp
```
