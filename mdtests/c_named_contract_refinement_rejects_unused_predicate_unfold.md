# Contract refinement rejects an unrelated predicate unfold

Naming an arbitrary predicate does not authorize the checked definition of a
different predicate embedded in the compared contract interface.

```c filename=unused_predicate_unfold.c
void clear_cell(int32* cell) {
    cell[0] = 0;
}
```

```click
verifying "unused_predicate_unfold.c";

predicate IsZero(cell: int32[]) {
    cell[0] == 0
}

predicate Irrelevant(value: int32) {
    value == value
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
        unfold(Irrelevant);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `SetsZero(&clear_cell)`
```
