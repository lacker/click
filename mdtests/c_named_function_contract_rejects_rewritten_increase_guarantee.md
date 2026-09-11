# A recorded equality that decides the clause false is not a refinement

The same `Decrease` clause as
`c_named_function_contract_refines_rewritten_decrease_guarantee`, with a
callback that adds one instead of subtracting it. Rewriting the clause's left
operand by the callback's recorded equality decides the comparison false, so
the rewrite must reject the refinement rather than accept any rewrite it can
find.

```c filename=rewritten_increase_step.c
void increment(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cell) {
    step(cell);
}

void rewritten_increase_caller(int32* cell) {
    apply_step(&increment, cell);
}
```

```click
verifying "rewritten_increase_step.c";

contract void Decrease(int32* cell) {
    requires 0 < cell[0];
    requires cell[0] < 100;
    owns cell[0..1];
    ensures cell[0] < old(cell[0]);
}

void increment(int32* state) {
    requires state[0] < 1000;
    owns state[0..1];
    ensures state[0] == old(state[0]) + 1;
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

void rewritten_increase_caller(int32* cell) {
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
fail: function `increment` does not satisfy named contract `Decrease`
```
