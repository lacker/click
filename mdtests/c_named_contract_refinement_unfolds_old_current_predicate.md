# Contract refinement unfolds a predicate over entry and current memory

Predicate arguments retain the shared function-entry and post-call snapshots
used by callback refinement. Opening the predicate therefore exposes the same
`old` and current cell values as the concrete callback guarantee.

```c filename=old_current_predicate_refinement.c
void increment_cell(int32* cell) {
    cell[0] += 1;
}
```

```click
verifying "old_current_predicate_refinement.c";

predicate Increased(before: int32, after: int32) {
    before < after
}

contract void MakesProgress(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    mutable cell[0..1];
    ensures Increased(old(cell[0]), cell[0]);
}

void increment_cell(int32* cell) {
    requires cell[0] < 1000;
    owns cell[0..1];
    mutable cell[0..1];
    ensures cell[0] == old(cell[0]) + 1;
} by {
    execute();
    frame();
    simp();
}

theorem increment_cell_makes_progress() {
    ensures MakesProgress(&increment_cell) by {
        unfold(MakesProgress);
        unfold(Increased);
        simp();
    }
}
```

```expect
pass
```
