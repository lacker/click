# `auto` refuses a bound that does not follow

`i < n` and `n <= 1000` do not give `to_integer(i) <= 998`: `i` may be 999.
The solver finds that model and declines, and `simp` misses too. (Reporting
the model in the failure is stage-1 milestone 5.)

```click
theorem does_not_follow(i: uint64, n: uint64) {
    requires i < n;
    requires n <= 1000u64;
    ensures to_integer(i) <= 998 by {
        have to_integer(i) <= 998 by auto;
        assumption();
    }
}
```

```expect
fail: could not complete tactic 1 (`have`)
```
