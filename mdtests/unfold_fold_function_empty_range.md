# unfolding a fold-bodied function over an empty range

`unfold(f(args)) using { ... }` opens one layer of a pure function whose body
is a range fold, but the layer it opens is the range-fold law the listed guards
select, stated over `f(args)` itself rather than over the fold the declaration
writes. With the empty-range guard listed, that layer is `f(args) == <initial>`.

Stating the law over the application is what makes it usable here. The fold's
body reads `p[k]` at the fold's own bound index, and a pure theorem cannot
lower that read at the proof site, so retyping the fold to hand it to
`integer_range_fold_empty` is not an option. The read stays inside the
function's declaration, where the theorem's own `viewable` premise covers it.

```click
function icount(p: int32[], lo: int32, hi: int32, x: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| {
        acc + to_integer(if p[k] == x { 1 } else { 0 })
    })
}

theorem icount_of_an_empty_range(p: int32[], lo: int32, hi: int32, x: int32) {
    requires hi <= lo;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures icount(p, lo, hi, x) == 0 by {
        unfold(icount(p, lo, hi, x)) using {
            hi <= lo;
        }
        simp();
    }
}
```

```expect
pass
```
