# explicit expression definedness for a simple statement step

`defined(expression)` expands to the exact kernel proposition describing when
the C expression evaluates normally. A reusable theorem can establish that
fact, after which the simple `step()` tactic needs no contextual search.

```c filename=defined_expression_step.c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "defined_expression_step.c";

theorem increment_is_defined(x: int32) {
    requires x < 2147483647;

    ensures defined(x + 1) by {
        simp();
    }
}

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures result == x + 1;
} by {
    apply(increment_is_defined(x));
    step();
    simp();
}
```

```expect
pass
```
