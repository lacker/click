# A contract-refinement theorem explicitly unfolds a stateful predicate

A concrete callback can establish a named memory predicate when the theorem
explicitly opens both the contract and the predicate definition. Predicate
definitions are not searched or unfolded implicitly by the refinement proof.

```c filename=predicate_contract_refinement.c
void clear_cell(int32* cell) {
    cell[0] = 0;
}

void invoke_clear(void (*callback)(int32*), int32* cell) {
    callback(cell);
}

void predicate_refinement_caller(int32* cell) {
    invoke_clear(&clear_cell, cell);
}
```

```click
verifying "predicate_contract_refinement.c";

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
        unfold(IsZero);
        simp();
    }
}

void invoke_clear(void (*callback)(int32*), int32* cell) {
    requires SetsZero(callback);
    owns cell[0..1];
    ensures IsZero(cell);
} by {
    execute();
    simp();
}

void predicate_refinement_caller(int32* cell) {
    owns cell[0..1];
    ensures IsZero(cell);
} by {
    apply(clear_cell_is_sets_zero());
    execute();
    simp();
}
```

```expect
pass
```
