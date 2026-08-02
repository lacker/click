# simple statement transition requires an exact prerequisite

The bound implies that addition cannot overflow, but `step() using {}` does not
ask the contextual solver to derive that execution prerequisite.

```c filename=simple_statement_step_requires_exact_prerequisite.c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "simple_statement_step_requires_exact_prerequisite.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures result > x;
} by {
    step() using {}
    simp();
}
```

```expect
fail: `step() using` produced undefined behavior: signed overflow
```
