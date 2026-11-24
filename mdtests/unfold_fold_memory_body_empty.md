# Ordinary unfolding retains the named fold equation

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
