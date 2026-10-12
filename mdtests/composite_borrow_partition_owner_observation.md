# Opening ownership does not separate it from its own observation

```c filename=observation.c
void update(int *p, int *q) { *p = 1; }
```
```click
verifying "observation.c";
resource cell(p: int*) { owns *p; }
void update(int* p, int* q) {
    owns cell(p);
    views cell(q);
    requires *p == 5;
    ensures *p == 5;
} by {
    unfold(cell(p));
    open(cell(q)) { execute(); }
    fold(cell(p));
    simp();
}
```
```expect
fail:left side evaluated to 1, right side evaluated to 5
```
