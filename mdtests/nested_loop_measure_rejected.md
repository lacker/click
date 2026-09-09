# a nested loop that raises the enclosing measure is not ranked

The inner loop raises `n` to 10 and the outer body lowers it to 9, so for any
`0 < n <= 100` this program never leaves the outer loop. The outer `decreases n`
was certified anyway: a variable a nested loop assigns had its alias dropped,
which restored the enclosing loop-head value instead of admitting that the
inner loop's final value is not known here.

Replacing the inner loop with the straight-line `n = 10;` it stands for is
rejected with the same diagnostic, which is what this program should get.

```c filename=nested_loop_measure_rejected.c
int32 nest(int32 n) {
    while (n > 0) {
        while (n < 10) {
            n = n + 1;
        }
        n = n - 1;
    }
    return n;
}
```

```click
verifying "nested_loop_measure_rejected.c";

int32 nest(int32 n) {
    requires n >= 0 and n <= 100;
    ensures result <= 0;
} by {
    loop {
        decreases n;
        invariant n <= 100;
        preserve by {
            loop {
                decreases 10 - n;
                invariant n >= 0 and n <= 100;
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: loop 0 does not decrease `n` to a nonnegative value
```
