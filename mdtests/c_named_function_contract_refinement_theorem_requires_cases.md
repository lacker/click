# Guarded contract refinement requires the written cases

Unfolding a contract does not make the kernel search for conditional-footprint
cases. When a concrete callback's mutable footprint is guarded, the theorem
must state the relevant split explicitly.

```c filename=refinement_theorem_requires_cases.c
void set_one_if_active(int32 active, int32* cell) {
    if (active != 0) {
        cell[0] = 1;
    }
}
```

```click
resource optional_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "refinement_theorem_requires_cases.c";

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

theorem missing_cases() {
    ensures MakePositive(&set_one_if_active) by {
        unfold(MakePositive);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `MakePositive(&set_one_if_active)`
```
