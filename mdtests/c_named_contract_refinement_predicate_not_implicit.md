# Stateful predicates are not unfolded during direct pointer formation

The concrete callback's scalar guarantee is definitionally sufficient, but a
direct address does not silently open the named contract's predicate. An
explicit refinement theorem must authorize that definition first.

```c filename=predicate_refinement_not_implicit.c
void clear_cell(int32* cell) {
    cell[0] = 0;
}

void invoke_clear(void (*callback)(int32*), int32* cell) {
    callback(cell);
}

void direct_predicate_caller(int32* cell) {
    invoke_clear(&clear_cell, cell);
}
```

```click
verifying "predicate_refinement_not_implicit.c";

predicate IsZero(cell: int32[]) {
    cell[0] == 0
}

contract void SetsZero(int32* cell) {
    owns cell[0..1];
    ensures IsZero(cell);
}

void clear_cell(int32* cell) {
    owns cell[0..1];
    ensures cell[0] == 0;
} by {
    execute();
    simp();
}

void invoke_clear(void (*callback)(int32*), int32* cell) {
    requires SetsZero(callback);
    owns cell[0..1];
    ensures IsZero(cell);
} by {
    execute();
    simp();
}

void direct_predicate_caller(int32* cell) {
    owns cell[0..1];
    ensures IsZero(cell);
} by auto;
```

```expect
fail: function `clear_cell` does not satisfy named contract `SetsZero`
```
