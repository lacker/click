# Stateful predicate refinement must be explicitly unfolded

The predicate body is not an implicit refinement rule. Merely opening the
named contract does not authorize the checker to use `IsZero`'s definition.

```c filename=predicate_refinement_requires_unfold.c
void clear_cell(int32* cell) {
    cell[0] = 0;
}
```

```click
verifying "predicate_refinement_requires_unfold.c";

predicate IsZero(cell: int32[]) {
    cell[0] == 0
}

contract void SetsZero(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
    ensures IsZero(cell);
}

void clear_cell(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
    ensures cell[0] == 0;
} by {
    execute();
    frame();
    simp();
}

theorem clear_cell_is_sets_zero() {
    ensures SetsZero(&clear_cell) by {
        unfold(SetsZero);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `SetsZero(&clear_cell)`
```
