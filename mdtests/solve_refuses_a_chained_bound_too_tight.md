# solve refuses a chained bound one too tight

The negative of `mdtests/solve_follows_a_bound_to_another_variable.md`:
`i < n` and `n <= 100` give `i <= 99`, so `i + 1 <= 100` holds but
`i + 1 <= 99` does not, and the chained selection does not prove it.

```c filename=solve_refuses_a_chained_bound_too_tight.c
int32 count_to(int32 n) {
    int32 i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "solve_refuses_a_chained_bound_too_tight.c";

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
            have to_integer(i + 1) <= 99;
            step();
        }
    }
}
```

```expect
fail: could not establish `to_integer((i + 1)) <= 99`
```
