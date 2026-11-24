# `by close();` on a function postcondition names the fix

`solve` reasons about the state at function exit and never runs the C body,
so a postcondition proved `by close();` is refused before any statement runs.
The refusal says what to write instead: a step to the exit first, or the
omitted proof, which executes and then closes. It is the same refusal
`solve` gets inside an execution arm
([`solve_before_exit_in_arm_names_the_frontier.md`](solve_before_exit_in_arm_names_the_frontier.md)).

```c filename=solve_before_execution.c
int32 clamp_low(int32 x) {
    if (x < 0) return 0;
    return x;
}
```

```click
verifying "solve_before_execution.c";

int32 clamp_low(int32 x) {
    ensures result >= 0 by close();
}
```

```expect
fail: Step to the exit first with `step_until(function.exit)` or `step()`
```
