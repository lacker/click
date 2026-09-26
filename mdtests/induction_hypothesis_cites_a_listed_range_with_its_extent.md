# An induction hypothesis's range premise is cited with its extent halves

The hypothesis `induct(hi) as ih` gives is the theorem's own statement at the
smaller argument, and that statement includes the extent halves of every range
it names: the theorem's proof assumed them, so a use of the theorem, including
a use by its own induction, owes them.

The range here does not move with the induction variable, so the halves the
hypothesis owes, `0 <= n - lo` and `n - lo <= 1073741823`, are the theorem's
own, available beside the stated range. Listing the range cites both of its
halves, by the rule every `apply using` shares, so the list names only what
the clause above it wrote. A theorem application is the same: the last theorem
lists `viewable(v[lo..n])` alone, although the theorem it applies owes both
halves of its `views` range and nothing else here states them. The negative,
where a moved range's halves are not available, is
`induction_hypothesis_owes_the_range_extent.md`.

```click
theorem hypothesis_cites_the_range_extent(v: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n >= 0 and viewable(v[lo..n]);
    ensures 0 <= hi by {
        induct(hi) as ih;
        if hi <= 0 {
            assumption();
        } else {
            have 0 < hi by { simp(); }
            have 0 <= hi - 1 by { arithmetic() using { 0 < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
            have hi - 1 <= n by { arithmetic() using { 0 < hi; hi <= n; } }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
                hi - 1 <= n;
                n >= 0 and viewable(v[lo..n]);
            }
            assumption();
        }
    }
}

theorem stated_range_extent_is_nonnegative(v: int32[], lo: int32, n: int32) {
    views v[lo..n];
    ensures 0 <= n - lo by { assumption(); }
}

theorem apply_cites_the_range_extent(v: int32[], lo: int32, n: int32) {
    views v[lo..n];
    ensures 0 <= n - lo by {
        apply(stated_range_extent_is_nonnegative(v, lo, n)) using {
            viewable(v[lo..n]);
        }
    }
}
```

```expect
pass
```
