# induction requires a nonnegative current measure

```click
theorem missing_domain(n: int32) {
    ensures n == n by {
        induct(n) as ih;
        simp();
    }
}
```

```expect
fail: requires a proof that `n` is nonnegative
```
