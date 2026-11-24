# Unfolding a fold-bodied function over an empty range

`unfold(f(args))` opens the empty-range equation when the context establishes
`hi <= lo`. The result is `f(args) == <initial>`; ordinary obligations handle
any remaining guards without a tactic-specific premise list.

```click quick-solve
function icount(p: int32[], lo: int32, hi: int32, x: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| {
        acc + to_integer(if p[k] == x { 1 } else { 0 })
    })
}

theorem icount_of_an_empty_range(p: int32[], lo: int32, hi: int32, x: int32) {
    requires hi <= lo;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures icount(p, lo, hi, x) == 0 by {
        unfold(icount(p, lo, hi, x));
        close();
    }
}
```

```expect
pass
```
