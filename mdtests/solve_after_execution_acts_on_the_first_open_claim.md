# `solve` after execution acts on the first open claim

After execution `close()` closes the first open goal, as the other closers do;
the implicit closer is the catch-all that closes every goal still open. Here `close()`
closes `result == 1` and leaves `result == n` for `normalize()`. When `solve`
closed every claim it could, `normalize()` was refused for having no goal.

```c filename=solve_after_execution_acts_on_the_first_open_claim.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "solve_after_execution_acts_on_the_first_open_claim.c";

int32 f(int32 n) {
    requires n == 1;
    ensures result == 1;
    ensures result == n;
} by {
    step_until(function.exit);
    close();
    close();
}
```

```expect
pass
```
