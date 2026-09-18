# `arithmetic()` adds `0 <= u` to `u <= v`

The plainest transitivity: `0 <= u` and `u <= v` give `0 <= v`. The certificate
the planner prints for the sum spells it as the two premises added side by
side, `(0 + u) <= (u + v)`. Lowering folds the zero away, so the left side is
read as `u`, and the check that accepts a printed sum knew a zero only on the
right addend. The step then failed as "does not encode the child sum",
although `simp()` closed the same goal at once.

```c filename=arithmetic_adds_a_premise_with_a_zero_side.c
int32 pass(int32 u, int32 v) {
    return v;
}
```

```click
verifying "arithmetic_adds_a_premise_with_a_zero_side.c";

int32 pass(int32 u, int32 v) {
    requires 0 <= u;
    requires u <= v;
    ensures result >= 0;
} by {
    have 0 <= v by { arithmetic() using { 0 <= u; u <= v; } }
    step();
    simp();
}
```

```expect
pass
```
