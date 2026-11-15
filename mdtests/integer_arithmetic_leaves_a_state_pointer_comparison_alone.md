# Integer arithmetic leaves a state pointer comparison alone

Under Integer specification arithmetic a comparison that does arithmetic compares
exact Integers, but a pointer comparison is not arithmetic on Integers:
`p == a + i` stays a comparison of addresses. That holds under `at(...)` as
well, which is how an expanded proof restates a pointer fact recorded at a
mark.

```c filename=integer_arithmetic_leaves_a_state_pointer_comparison_alone.c
int step(int *a, int i) {
    int *p = a + i;
    i = i + 1;
    return *p;
}
```

```click

verifying "integer_arithmetic_leaves_a_state_pointer_comparison_alone.c";
int32 step(int32* a, int32 i) {
    requires 0 <= i and i < 4;
    views a[0..4];
} by {
    step_until(assignment(i, 0));
    mark start;
    step();
    have at(start, p) == at(start, a + i);
}
```

```expect
pass
```
