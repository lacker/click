# A proof `if` after execution that would fork the proof is refused

After `step_until(function.exit)`, `n < 5` is not decided on the function's one outcome path,
so each arm would be a separate path. What follows a proof `if` is checked
once: the `close()` after this one would instead run once per arm, and a run of
such `if`s would check the rest of the proof once per combination of arms.
The `if` is refused, as an execution-frontier `if` whose arms do not rejoin
is (`proof_if_arms_must_rejoin.md`).

```c filename=a_proof_if_after_execution_that_would_fork_is_refused.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "a_proof_if_after_execution_that_would_fork_is_refused.c";

int32 f(int32 n) {
    requires 0 <= n;
    requires n <= 10;
    ensures result <= 10;
    ensures result >= 0;
} by {
    step_until(function.exit);
    if n < 5 {
        have n <= 10 by close();
    } else {
        have n <= 10 by close();
    }
    close();
}
```

```expect
fail: the arms of this proof `if` after execution do not rejoin
```
