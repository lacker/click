# a pure recursion measure still has to descend

The measure is the same pure application
[`c_decreases_pure_expression_recursion.md`](c_decreases_pure_expression_recursion.md)
ranks the recursion by, and its nonnegativity closes for the same reason. What
the body never does is lower what the measure reads: it passes `n` unchanged.
The recursive call therefore compares the measure against itself, and the
descent member stays open. A pure measure buys no leniency: the obligation is
the one a parameter measure's analysis would refuse.

```c filename=c_decreases_pure_expression_recursion_must_descend.c
int32 drain(int32 n) {
    int32 result;
    if (n > 0) {
        result = drain(n);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_pure_expression_recursion_must_descend.c";

function level(n: int32) -> int32 {
    n
}

int32 drain(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    branch {
        then {
            have 0 <= level(n) by { unfold(level(n)); simp(); }
            step();
            step();
            simp();
        }
        else {}
    }
    step();
    simp();
}
```

```expect
fail: `level(n)` decreases at the recursive call
```
