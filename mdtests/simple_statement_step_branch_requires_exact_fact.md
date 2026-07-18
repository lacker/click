# Simple statement branch step requires an exact condition fact

Contextual arithmetic can imply a branch condition without providing the exact
condition fact. That reasoning belongs to `execute_step()`, not `step()`.

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
        step();
        step();
        simp();
    }
}
```

```expect
fail: `step` could not prove that the next C `if` condition `flag` is one exact truth value
```
