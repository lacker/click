# Ordinary simp works after an unrelated predicate unfold

The ordinary proof engine accepts the same logical tactics after opening a
contract. The closing smart tactic can prove this true claim even though the
preceding predicate unfold was unnecessary.

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
        unfold(Irrelevant);
        simp();
    }
}
```

```expect
pass
```
