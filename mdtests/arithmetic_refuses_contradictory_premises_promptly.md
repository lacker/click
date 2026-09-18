# arithmetic refuses contradictory premises promptly

`arithmetic()` plans an interval for every operand it needs defined. Premises
that contradict each other, here `x < 0` beside the requirement `x >= 0`, bound
`x` into an empty interval. Planning one anyway produced a certificate the
kernel then refused, so the user saw a certificate rejection rather than a
statement about the arithmetic. The planner declines the empty interval
instead, and the tactic reports its own prompt failure.

```c filename=arithmetic_refuses_contradictory_premises_promptly.c
int32 pick(int32 x, int32 y) {
    return y;
}
```

```click
verifying "arithmetic_refuses_contradictory_premises_promptly.c";

int32 pick(int32 x, int32 y) {
    requires x >= 0 and y >= 0 and y <= 2147483647;
    ensures result == y;
} by {
    have x < 0 implies y < y - x by { intro(); arithmetic() using { x < 0; x >= 0; } }
    step();
    simp();
}
```

```expect
fail: `arithmetic` cannot establish that every int32 operation in the current goal is defined without overflow from exactly the listed premises
```
