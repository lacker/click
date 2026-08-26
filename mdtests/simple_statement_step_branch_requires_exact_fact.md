# A statement step decides a branch from the proof context

Every statement step executes with the proof context visible to the
kernel. `requires flag > 0` does not state `flag != 0` exactly, but the
kernel decides the condition from it, so both the explicit `step() using
{}` and the bare `step()` enter the selected arm.

```c filename=simple_statement_step_branch_requires_exact_fact.c
int32 positive_branch(int32 flag) {
    if (flag) {
        return 1;
    } else {
        return 0;
    }
}
```

```click
verifying "simple_statement_step_branch_requires_exact_fact.c";

int32 positive_branch(int32 flag) {
    requires flag > 0;
    ensures result == 1 by {
        step() using {}
        step();
        simp();
    }
}
```

```expect
pass
```
