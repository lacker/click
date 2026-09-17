# Refinement rewrites the left operand of a clause by a recorded equality

`Decrease` promises `cell[0] < old(cell[0])`, so the clause's left operand is
the new value, and `decrement` guarantees an equality for exactly that value.
The refinement holds only under that rewrite, and the rewrite is the proof's
step, not a kernel search: the refinement theorem cites the equality with
`rewrite`, and `click expand` prints it. Deleting it from the certificate is
rejected in
`c_named_function_contract_refinement_rejects_missing_rewrite`.

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

theorem decrement_is_decrease() {
    ensures Decrease(&decrement) by {
        unfold(Decrease);
        simp();
    }
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
    apply(decrement_is_decrease());
    execute();
    simp();
}
```

```expect
pass
```
