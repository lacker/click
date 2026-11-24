# `step()` refuses a maybe-throwing call

A maybe-throwing call has two successors, so one linear `step()` cannot
take it, just as it cannot take an undecided C `if`. The refusal names the
call and the `outcomes` form that proves its two arms;
`mdtests/outcomes_routes_a_throw_that_leaves_the_function.md` writes it.

```c filename=step_refuses_a_maybe_throwing_call.c
int32 helper(int32 x) { return x; }
int32 caller(int32 x) {
    int32 y = helper(x);
    y = x;
    return y;
}
```

```click
verifying "step_refuses_a_maybe_throwing_call.c";

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
} by {
    step();
    step();
    step();
    step();
    close();
}
```

```expect
fail: which may throw; its returned and threw successors are separate proof arms
```
