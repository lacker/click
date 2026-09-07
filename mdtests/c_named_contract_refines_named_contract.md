# One named callback contract can refine another

A theorem can relate contracts for an arbitrary function-pointer value. The
source callback increments one cell exactly; the target interface promises
only progress and transfers a larger pair. Refinement frames the unused cell
and accepts the source's smaller mutable footprint. The theorem is then
applied to an abstract callback—no concrete target or project scan is
involved.

```c filename=abstract_contract_refinement.c
void apply_progress(void (*step)(int32*), int32* cells) {
    step(cells);
}

void abstract_contract_refinement_caller(
    void (*step)(int32*),
    int32* cells
) {
    apply_progress(step, cells);
}
```

```click
verifying "abstract_contract_refinement.c";

contract void ExactIncrement(int32* cell) {
    requires cell[0] < 1000;
    owns cell[0..1];
    mutable cell[0..1];
    ensures cell[0] == old(cell[0]) + 1;
}

contract void ProgressPair(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..2];
    mutable cells[0..2];
    ensures old(cells[0]) < cells[0];
}

theorem exact_increment_is_progress(
    step: void (*)(int32*)
) {
    requires ExactIncrement(step);
    ensures ProgressPair(step) by {
        unfold(ExactIncrement);
        unfold(ProgressPair);
        simp();
    }
}

void apply_progress(void (*step)(int32*), int32* cells) {
    requires ProgressPair(step);
    requires cells[0] < 100;
    owns cells[0..2];
    mutable cells[0..2];
    ensures old(cells[0]) < cells[0];
} by {
    execute();
    frame();
    simp();
}

void abstract_contract_refinement_caller(
    void (*step)(int32*),
    int32* cells
) {
    requires ExactIncrement(step);
    requires cells[0] < 100;
    owns cells[0..2];
    mutable cells[0..2];
    ensures old(cells[0]) < cells[0];
} by {
    apply(exact_increment_is_progress(step));
    execute();
    frame();
    simp();
}
```

```expect
pass
```
