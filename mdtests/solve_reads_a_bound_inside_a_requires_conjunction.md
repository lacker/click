# solve reads a bound inside a requires conjunction

`x + 1 >= 0` needs both of `x`'s bounds: `x >= 0` for the sign and
`x <= 100` so the increment cannot overflow. Each leaf conjunct of a fact is
itself an available fact, so the conjunction provides both bounds exactly as
separate `requires` lines would, and solve finds them through `x`'s indexed
bound bucket at function exit. `inc_extracted` shows that an explicit
`have` of a leaf conjunct is accepted after execution but adds nothing.

```c filename=solve_reads_a_bound_inside_a_requires_conjunction.c
int32 inc(int32 x) {
    return x + 1;
}

int32 inc_extracted(int32 x) {
    return x + 1;
}
```

```click
verifying "solve_reads_a_bound_inside_a_requires_conjunction.c";

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 0;
}

int32 inc_extracted(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 0;
} by {
    step_until(function.exit);
    have x <= 100;
    close();
}
```

```expect
pass
```
