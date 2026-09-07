# Predicate unfolding composes with explicit refinement cases

Opening a stateful predicate remains in scope for both arms of a written
refinement case split. The proof chooses the conditional resource case; the
checker does not enumerate it.

```c filename=predicate_unfold_before_cases.c
void clear_if_active(int32 active, int32* cell) {
    if (active != 0) {
        cell[0] = 0;
    }
}
```

```click
resource optional_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "predicate_unfold_before_cases.c";

predicate ActiveIsZero(active: int32, cell: int32[]) {
    active != 0 implies cell[0] == 0
}

contract void ClearsWhenActive(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures ActiveIsZero(active, cell);
}

void clear_if_active(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] == 0;
} by {
    if active != 0 {
        unfold(optional_cell(active, cell));
        execute();
        fold(optional_cell(active, cell));
        simp();
    } else {
        unfold(optional_cell(active, cell));
        execute();
        fold(optional_cell(active, cell));
        simp();
    }
}

theorem clear_if_active_satisfies_contract() {
    ensures ClearsWhenActive(&clear_if_active) by {
        unfold(ClearsWhenActive);
        unfold(ActiveIsZero);

        if active != 0 {
            simp();
        } else {
            simp();
        }
    }
}
```

```expect
pass
```
