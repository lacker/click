# an induction hypothesis owes its range premise's extent

The hypothesis `induct(hi) as ih` gives is the theorem's own statement at the
smaller argument, and that statement includes the byte-count guards of every
range it names: the theorem's proof assumed them, so a use of the theorem —
including a use by its own induction — has to supply them.

The range here does not move with the induction variable, so the guards the
hypothesis owes are the theorem's own, already available. They still have to be
listed, because `apply … using` is restricted to exactly what it names. Omitting
one is refused, with the premise spelled in the reader's names rather than as a
kernel condition.

```click
theorem hypothesis_owes_the_range_extent(v: int32[], lo: int32, n: int32, hi: int32) {
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
```

```expect
fail: instantiated premise `0 <= (n - lo) is true` does not follow from the listed evidence
```
