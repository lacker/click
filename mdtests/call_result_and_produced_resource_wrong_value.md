# Naming a produced resource does not justify a false C return value

The C uses the returned flag in a condition. The proof keeps the newly
produced cell and the flag from the same checked call, then returns the cell.

```c filename=status.c
int32 set(int32 *p) { *p = 1; return 1; }
void caller(int32 *p) { if (set(p)) return; }
```
```click
verifying "status.c";
resource Cell(p: int32*) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
}
int32 set(int32* p) {
    consumes input: Cell(p);
    produces output: Cell(p);
    ensures output.value == 1;
    ensures result == 1;
} by {
    unfold(input);
    step_until(function.exit);
    let output = fold(Cell(p), { value: 1 });
    solve();
}
void caller(int32* p) {
    consumes input: Cell(p);
    produces checked: Cell(p);
    ensures checked.value == 1;
} by {
    let { result: status, output: checked } = step(set, { input: input });
    have status == 2 by { known(); }
}
```
```expect
fail: `known()` could not close the current goal
```
