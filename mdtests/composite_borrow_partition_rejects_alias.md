# A composite cannot be transferred and lent over the same cell

Opening composites exposes separation only after the caller has supplied a
valid ownership partition. A caller cannot discharge that partition by passing
one owned cell to both parameters.

```c filename=alias.c
void update(int *p, int *q) { *p = 1; }
void caller(int *p) { update(p, p); }
```
```click
verifying "alias.c";
resource cell(p: int*) { owns *p; }
void update(int* p, int* q) {
    owns cell(p);
    views cell(q);
    ensures *q == old(*q);
} by {
    unfold(cell(p));
    with(cell(q)) { step_until(function.exit); }
    fold(cell(p));
    close();
}
void caller(int* p) {
    owns cell(p);
    ensures 1 == 1;
} by { step_until(function.exit); close(); }
```
```expect
fail:A required resource overlaps a live borrow.
```
