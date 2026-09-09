# Construct and update a cell model from memory

Explicit folding consumes the body ownership and checks all proposed fields.
Initial construction does not require an earlier unfold.

```c filename=resource_cell_construction.c
void init(int32* p, int32 value) { *p = value; }
void set(int32* p, int32 value) { *p = value; }
```

```click
verifying "resource_cell_construction.c";

resource cell(p: int32*) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
}

void init(int32* p, int32 value) {
    consumes p[0..1];
    produces c: cell(p);
    ensures c.value == value;
} by {
    execute();
    let c = fold(cell(p), { value: value });
    simp();
}

void set(int32* p, int32 value) {
    owns c: cell(p);
    ensures c.value == value;
} by {
    unfold(c);
    execute();
    let c = fold(cell(p), { value: value });
    simp();
}
```

```expect
pass
```
