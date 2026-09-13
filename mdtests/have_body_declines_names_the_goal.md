# A `have` whose body does not close its goal names the goal and the step

A mid-execution `have` first runs its written body as a checked proof and then,
for a smart body, a generated plan. When neither route closes the goal the
author needs to know which goal and which written step; the previous message,
"body did not construct a completed proof object", named neither and read as an
internal failure rather than a proof failure.

A written step that fails outright still reports its own checked error, which is
more specific. This fixture pins the remaining case: a body the checked driver
declines without an error of its own. `simp()` closes a goal and is therefore
checked only as the last step of a body, so a `simp()` with a step after it is a
shape the driver does not run.

```c filename=have_body_declines_names_the_goal.c
int spin(int n) {
    return n;
}
```

```click
verifying "have_body_declines_names_the_goal.c";

int spin(int n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    have n + 1 > 500 by {
        simp();
        normalize();
    }
    execute();
}
```

```expect
fail: `have (n + 1) > 500` was not proved: its body is not a shape the checked driver runs
```
