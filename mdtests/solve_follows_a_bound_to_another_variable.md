# solve follows a bound to another variable

In the loop body, `i + 1 <= 101` needs `i`'s bounds and then the bound on
the variable they name: `i < n` from the guard, and `n <= 100` from the
contract. solve's bound selection follows bounds from the goal's variables
to the variables they name, up to a fixed number of variables, and closes
the goal with one arithmetic step.

```c filename=solve_follows_a_bound_to_another_variable.c
int32 count_to(int32 n) {
    int32 i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "solve_follows_a_bound_to_another_variable.c";

int32 count_to(int32 n) {
    requires n >= 0 and n <= 100;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        initialize by { close(); }
        maintain by {
            have to_integer(i + 1) <= 101;
            step();
        }
    }
}
```

```expect
pass
```
