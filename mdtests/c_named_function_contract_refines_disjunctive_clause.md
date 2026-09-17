# A disjunctive contract clause is refined by naming its arm

`Stable` promises that the cell either keeps its value or grows. `increment`
always grows it, so the clause is refined through the right arm only. The arm
is the proof's choice, not the kernel's: `click expand` prints the `right()`
that selects it, and the certificate records which arm was taken.

```c filename=disjunctive_step.c
void increment(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void disjunctive_clause_caller(int32* cell) {
    apply_step(&increment, cell);
}
```

```click
verifying "disjunctive_step.c";

contract void Stable(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] == old(cell[0]) or old(cell[0]) < cell[0];
}

void increment(int32* state) {
    requires state[0] < 1000;
    owns state[0..1];
    ensures state[0] == old(state[0]) + 1;
} by {
    execute();
    simp();
}

theorem increment_is_stable() {
    ensures Stable(&increment) by {
        unfold(Stable);
        simp();
    }
}

void apply_step(void (*step)(int32*), int32* cell) {
    requires Stable(step);
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] == old(cell[0]) or old(cell[0]) < cell[0];
} by {
    execute();
    simp();
}

void disjunctive_clause_caller(int32* cell) {
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] == old(cell[0]) or old(cell[0]) < cell[0];
} by {
    apply(increment_is_stable());
    execute();
    simp();
}
```

```expect
pass
```
