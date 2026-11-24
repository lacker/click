# Scalar induction keeps fixed Integer parameters

The induction hypothesis varies the native measure and retains the same
mathematical seed, including requirements on that seed. The step retains
`previous + 0`, so its last tactic uses arithmetic and the induction
hypothesis rather than context-free normalization.

```click
function carry_seed(n: int32, seed: Integer) -> Integer {
    (0..n).fold(seed, |acc, k| { acc + to_integer(0) })
}

theorem carry_seed_returns_the_same_integer(n: int32, seed: Integer) {
    requires 0 <= n;
    requires 0 < seed;
    ensures carry_seed(n, seed) == seed by {
        let ih = induct(n);
        if n <= 0 {
            unfold(carry_seed(n, seed));
            close();
        } else {
            have 0 < n by close();
            have 0 <= to_integer(n - 1) by close() using { 0 < n; };
            have to_integer(n - 1) < 2147483647 by close() using { 0 < n; };
            have to_integer(n - 1) < to_integer(n);
            apply(ih(n - 1));
            unfold(carry_seed(n, seed));
            close();
        }
    }
}
```

```expect
pass
```
