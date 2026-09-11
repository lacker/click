# Refinement rewrites the left operand of a clause by a recorded equality

`Decrease` promises `cell[0] < old(cell[0])`, so the clause's left operand is
the new value, and `decrement` records an equality for exactly that value. The
clause is refined by rewriting the left operand through its recorded equality
class and deciding the rewritten comparison. Only equalities already recorded
in the refinement context may be used; the kernel does not search for a
derivation of one.

```c filename=rewritten_decrease_step.c
void decrement(int32* state) {
    state[0] -= 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void rewritten_decrease_caller(int32* cell) {
    apply_step(&decrement, cell);
}
```

```click
verifying "rewritten_decrease_step.c";

contract void Decrease(int32* cell) {
    requires 0 < cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] < old(cell[0]);
}

void decrement(int32* state) {
    requires 0 < state[0];
    owns state[0..1];
    ensures state[0] == old(state[0]) - 1;
} by {
    execute();
    simp();
}

void apply_step(void (*step)(int32*), int32* cell) {
    requires Decrease(step);
    requires 0 < cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] < old(cell[0]);
} by {
    execute();
    simp();
}

void rewritten_decrease_caller(int32* cell) {
    requires 0 < cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] < old(cell[0]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
