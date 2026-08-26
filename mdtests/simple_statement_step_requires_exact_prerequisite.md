# a statement step proves its prerequisites from the proof context

A bare `step()` executes the next statement with every fact in the proof
context visible to the kernel. The requirement bounds `x`, so the kernel
proves the addition cannot overflow without the step naming any premise.

```c filename=simple_statement_step_requires_exact_prerequisite.c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "simple_statement_step_requires_exact_prerequisite.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures result == x + 1;
} by {
    step();
    simp();
}
```

```expect
pass
```
