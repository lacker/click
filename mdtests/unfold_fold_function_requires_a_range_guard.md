# unfolding a fold-bodied function needs a guard that decides the range

Which equation `peel(f(args)) using { ... }` opens is decided by the listed
guards, and by nothing else. Here the append form's second guard is missing, so
neither equation is available. The refusal names what each form still wants
rather than picking one silently.

```click
function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

theorem icount_needs_a_range_guard(p: int32[], lo: int32, hi: int32) {
    requires 0 < hi;
    requires lo <= hi - 1;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures 0 <= icount(p, lo, hi) by {
        peel(icount(p, lo, hi)) using {
            lo <= hi - 1;
        }
        simp();
    }
}
```

```expect
fail: found no listed guard that decides the range. The empty-range equation needs `hi <= lo`; the append-last-cell equation needs `hi - 1 < 2147483647`
```
