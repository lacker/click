# `arithmetic()` adds a `>`-spelled premise

`a > 0` and `b >= 0` give `0 < a + b`. The printed certificate renders the sum
by adding the two premises side by side, but only `>=` was rewritten into the
ordered `<=` form before the addends were paired. A `>`-spelled premise kept
its "greater" side order, so the sum printed the `a` side against the `0` side
and the step failed as "does not encode the child sum", although restating the
premise as `0 < a` first closed the identical goal.

```c filename=arithmetic_adds_a_greater_than_premise.c
int32 sharpen(int32 a, int32 b) {
    return 0;
}
```

```click
verifying "arithmetic_adds_a_greater_than_premise.c";

int32 sharpen(int32 a, int32 b) {
    requires a > 0;
    requires a <= 1;
    requires b >= 0;
    requires b <= 1;
    ensures result == 0;
} by {
    have 0 < a + b by { arithmetic() using { a > 0; b >= 0; a <= 1; b <= 1; } }
    step();
    simp();
}
```

```expect
pass
```
