# `arithmetic()` bounds an operand through another premise

`0 <= i` and `i < n` keep `n - i` inside `int32`: together they say `n >= 1`.
The checker used to bound each operand only by premises naming that operand
alone, so `n` had the whole `int32` range, `n - i` looked able to overflow,
and the step failed as unable to establish definedness. A bound one premise
states through another atom is now one addition away, which the certificate
already knows how to print and check: the premise relating the two atoms
added to the other atom's own bound.

```c filename=arithmetic_bounds_an_atom_through_another.c
int32 gap(int32 n, int32 i) {
    return 0;
}
```

```click
verifying "arithmetic_bounds_an_atom_through_another.c";

int32 gap(int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    ensures result == 0;
} by {
    have 1 <= n - i by { arithmetic() using { 0 <= i; i < n; } }
    have n - i - 1 < n - i by { arithmetic() using { i >= 0; i < n; } }
    step();
    simp();
}
```

```expect
pass
```
