# `step()` refuses a C `if` the proof context does not decide

`step()` takes one statement into one successor. At a C `if` it enters the
arm the proof context decides; here nothing bounds `x`, so both condition
paths are feasible and the step is refused, naming the condition each path
assumes. `branch { true => { ... } false => { ... } }` or a proof `if` on the condition proves
both arms; `simple_statement_step_branch_requires_exact_fact.md` shows a
context that decides the same kind of condition.

```c filename=step_refuses_an_undecided_c_if.c
int32 sign(int32 x) {
    if (x > 3) {
        return 1;
    }
    return 0;
}
```

```click
verifying "step_refuses_an_undecided_c_if.c";

int32 sign(int32 x) {
    ensures result == 1 or result == 0;
} by {
    step();
    step();
    close();
}
```

```expect
fail: could not prove that the next C `if` condition `(x > 3)` is one exact truth value; got 2 feasible condition paths
```
