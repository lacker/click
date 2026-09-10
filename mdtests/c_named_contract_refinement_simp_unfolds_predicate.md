# Ordinary simp records the predicate unfolding needed by refinement

Opening the contract does not itself unfold the predicate. Ordinary `simp`
can select its checked unfolding, just as in other proposition proofs.

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
    ensures IsZero(cell);
}

void clear_cell(int32* cell) {
    owns cell[0..1];
    ensures cell[0] == 0;
} by {
    execute();
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
pass
```
