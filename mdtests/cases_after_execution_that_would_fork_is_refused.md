# A `cases` after execution that would fork is refused

When no disjunct is decided on an outcome path, a `cases` after execution forks that path, and its arms do not rejoin. Tactics written after it would then be checked once per arm, so the `cases` is refused.

```c filename=cases_after_execution_that_would_fork_is_refused.c
int32 f(int32 x) {
    return x;
}
```

```click
verifying "cases_after_execution_that_would_fork_is_refused.c";

int32 f(int32 x) {
    requires x == 1 or x == 2;
    ensures result >= 1;
} by {
    step_until(function.exit);
    cases {
        x == 1 => { }
        x == 2 => { }
    }
    close();
}
```

```expect
fail: the arms of this `cases` after execution do not rejoin
```
