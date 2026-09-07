# A theorem can prove that a concrete function satisfies a named contract

Behavioral refinement is an explicit, reusable pure theorem. Unfolding the
named contract introduces its arbitrary call parameters; the proof chooses the
conditional-resource cases rather than asking contract formation to enumerate
them implicitly.

```c filename=contract_refinement_theorem.c
void set_one_if_active(int32 active, int32* cell) {
    if (active != 0) {
        cell[0] = 1;
    }
}

void apply_positive(
    void (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    callback(active, cell);
}

void refinement_theorem_caller(int32* cell) {
    apply_positive(&set_one_if_active, 1, cell);
}
```

```click
resource optional_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "contract_refinement_theorem.c";

contract void MakePositive(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] > 0;
}

void set_one_if_active(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] == 1;
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

theorem set_one_is_make_positive() {
    ensures MakePositive(&set_one_if_active) by {
        unfold(MakePositive);

        if active != 0 {
            simp();
        } else {
            simp();
        }
    }
}

void apply_positive(
    void (*callback)(int32, int32*),
    int32 active,
    int32* cell
) {
    requires MakePositive(callback);
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] > 0;
} by {
    if active != 0 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}

void refinement_theorem_caller(int32* cell) {
    owns optional_cell(1, cell);
    ensures cell[0] > 0;
} by {
    apply(set_one_is_make_positive());
    execute();
    simp();
}
```

```expect
pass
```
