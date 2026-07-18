# Simple statement step enters an exact branch

`step()` can advance through a C `if` when an exact pure fact determines its
condition. It enters the selected arm without executing the arm body.

```c filename=simple_statement_step_branch.c
int32 choose_one(int32 flag) {
    if (flag) {
        return 1;
    } else {
        return 0;
    }
}
```

```c filename=simple_statement_step_else_branch.c
int32 choose_zero(int32 flag) {
    if (flag) {
        return 1;
    } else {
        return 0;
    }
}
```

```click
verifying "simple_statement_step_branch.c";
verifying "simple_statement_step_else_branch.c";

int32 choose_one(int32 flag) {
    requires flag != 0;
    ensures result == 1 by {
        step();
        step();
        simp();
    }
}

int32 choose_zero(int32 flag) {
    requires flag == 0;
    ensures result == 0 by {
        step();
        step();
        simp();
    }
}
```

```expect
pass
```
