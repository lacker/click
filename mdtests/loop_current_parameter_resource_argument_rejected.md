# Current loop resource arguments follow the updated cursor

```c filename=advance.c
void advance(int32 *rb, int32 *stop) {
    while (rb != stop) {
        rb = stop;
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
function remaining(rb: int32*, stop: int32*) -> int32 {
    if rb == stop { 0 } else { 1 }
}
void advance(int32* rb, int32* stop) {
    owns cell: Cell(rb);
    ensures cell.value == old(cell.value);
} by {
    loop {
        decreases remaining(rb, stop);
        owns cell: Cell(rb);
        invariant cell.value == old(cell.value);
        initialize by close();
        maintain by {
            step();
        }
    }
}
```
```expect
fail: loop binder `cell` has no owned `Cell` instance at its arguments here
```
