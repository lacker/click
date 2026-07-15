# proof steps prepare execution

These checks require deterministic pure proof steps inside an execution proof
to update its current facts before the following C statement is executed.

```c filename=proof_steps_prepare_execution.c
int32 increment_unfold(int32 x) {
    return x + 1;
}
```

```c filename=proof_steps_prepare_execution_apply.c
int32 increment_apply(int32 x) {
    return x + 1;
}
```

```c filename=proof_steps_prepare_execution_have.c
int32 increment_have(int32 x) {
    return x + 1;
}
```

```click
verifying "proof_steps_prepare_execution.c";
verifying "proof_steps_prepare_execution_apply.c";
verifying "proof_steps_prepare_execution_have.c";

predicate incrementable(int32 x) {
    x < 2147483647
}

theorem incrementable_bound(x: int32) {
    requires incrementable(x);

    ensures x < 2147483647 by {
        unfold(incrementable);
        simp();
    }
}

int32 increment_unfold(int32 x) {
    requires incrementable(x);

    ensures result == x + 1 by {
        unfold(incrementable);
        execute_step();
        simp();
    }
}

int32 increment_apply(int32 x) {
    requires incrementable(x);

    ensures result == x + 1 by {
        apply(incrementable_bound(x));
        execute_step();
        simp();
    }
}

int32 increment_have(int32 x) {
    requires incrementable(x);

    ensures result == x + 1 by {
        have x < 2147483647 by {
            unfold(incrementable);
            simp();
        }
        execute_step();
        simp();
    }
}
```

```expect
pass
```
