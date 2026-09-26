# An induction hypothesis owes a moved range's extent

The hypothesis `induct(hi) as ih` gives is the theorem's own statement at the
smaller argument, and that statement includes the extent halves of every range
it names: the theorem's proof assumed them, so a use of the theorem, including
a use by its own induction, owes them.

Listing a range cites its halves only where they are available. Here the range
moves with the induction variable: the hypothesis names `v[lo..hi - 1]`, a
range this proof narrowed to rather than one a clause stated, so its halves
`0 <= hi - 1 - lo` and `hi - 1 - lo <= 1073741823` are facts nobody has
established. Omitting them is refused, with the premise spelled in the
reader's names. The positive, where the halves come with a stated range, is
`induction_hypothesis_cites_a_listed_range_with_its_extent.md`.

```click
theorem hypothesis_owes_the_range_extent(v: int32[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= 1073741823;
    ensures 0 <= hi by {
        induct(hi) as ih;
        if hi <= lo {
            assumption();
        } else {
            have lo < hi by { simp(); }
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= 1073741823 by {
                arithmetic() using { 0 <= hi; hi <= 1073741823; }
            }
            have viewable(v[lo..hi - 1]) by { simp(); }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                viewable(v[lo..hi - 1]);
                0 <= lo;
                hi - 1 <= 1073741823;
            }
            assumption();
        }
    }
}
```

```expect
fail: instantiated premise `0 <= ((hi - 1) - lo) is true` does not follow from the listed evidence
```
