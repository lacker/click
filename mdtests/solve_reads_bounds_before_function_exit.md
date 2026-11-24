# solve reads a variable's bounds before function exit

solve proves `x + 1 >= 1` from both of `x`'s bounds wherever it runs: in a
`have` before execution, from a `requires` conjunction or from separate
`requires` lines, and inside a `branch` arm, where the negated branch
condition `not (x > 100)` gives the upper bound. Each reads `x`'s indexed
bound bucket, as solve already did at function exit. A loop bundle closer is
the exception: its members cite only the loop head and the contract.

```c filename=solve_reads_bounds_before_function_exit.c
int32 conjunction(int32 x) {
    return x + 1;
}

int32 separate(int32 x) {
    return x + 1;
}

int32 in_arm(int32 x) {
    if (x > 100) {
        return 0;
    }
    return x + 1;
}
```

```click
verifying "solve_reads_bounds_before_function_exit.c";

int32 conjunction(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 0 by {
        have to_integer(x + 1) >= 1;
    }
}

int32 separate(int32 x) {
    requires x >= 0;
    requires x <= 100;
    ensures result >= 0 by {
        have to_integer(x + 1) >= 1;
    }
}

int32 in_arm(int32 x) {
    requires x >= 0;
    ensures result >= 0 by {
        branch {
            true => {
                step();
                close();
            }
            false => {
                have to_integer(x + 1) >= 1;
            }
        }
        step();
        close();
    }
}
```

```expect
pass
```
