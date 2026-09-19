# `have viewable(...)` proves a prefix of a viewable range

A viewability fact was findable but not provable. The kernel would place a cell
inside `viewable(v[lo..hi])` on its own whenever the index bounds were stated
order facts, but writing that same conclusion down as a goal —
`have viewable(v[lo..hi - 1]) by { ... }` — had no proof step to go through. The
implicit method and the explicit method disagreed about one fact, and the
explicit one is the method the language tells users to reach for when the
verifier cannot see something.

They agree now, through one decision. Range narrowing reads both extents at
element granularity: the premise covers the elements `lo..hi`, the goal names
the elements `lo..hi - 1`, and the order facts `lo <= hi - 1` and
`hi - 1 <= hi` place the second inside the first. That is the same kernel
viewability decision the implicit check asks, so the explicit proof accepts
everything the implicit check accepts.

An extent is modular arithmetic, so the rule also needs the assumed range to be
a valid 32-bit byte extent: its element count has to sit in `0..=1073741823`,
which for four-byte elements is what keeps `(hi - lo) * 4` from wrapping.
Without that a range whose count is `1 << 30` has an extent of `0` bytes —
vacuously viewable — and narrowing it would manufacture a real cell from
nothing.

That bound is not restated here. `requires hi >= 0 and viewable(v[lo..hi])`
states the range, and a stated range means both halves of what it says: that
`lo..hi` is a valid byte extent, and that those bytes are viewable. The proof
below writes only the order facts placing the goal inside the premise.

The order facts come first, each proved on its own, and then the viewability
goal is discharged against them — the ordinary `have`-before-the-step shape of
`mdtests/pure_have_sees_proved_facts.md`, with a `viewable` goal this time.

```click
theorem prefix_of_a_viewable_range(v: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(v[lo..hi]);
    ensures viewable(v[lo..hi - 1]) by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        simp();
    }
}
```

```expect
pass
```
