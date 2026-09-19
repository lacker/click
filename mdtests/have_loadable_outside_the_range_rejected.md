# a `loadable` goal outside the assumed range is refused, by name

Range narrowing concludes `loadable(v[lo..k])` from `loadable(v[lo..hi])` only
when order facts place `[lo, k)` inside `[lo, hi)`. Here `lo <= k` is stated and
`k <= hi` is not, so the goal's upper end is not known to be inside the assumed
range and the step is refused.

The refusal names the missing fact in the spelling the theorem uses, because
that is what the reader has to prove next. It does not print two lowered byte
extents and leave the arithmetic to them.

```click
theorem range_not_inside_a_loadable_range(v: int32[], lo: int32, hi: int32, k: int32) {
    requires 0 <= lo;
    requires lo <= k;
    requires hi >= 0 and loadable(v[lo..hi]);
    ensures loadable(v[lo..k]) by {
        extract(loadable(v[lo..hi]));
        transport(loadable(v[lo..hi]), loadable(v[lo..k])) using {
            loadable(v[lo..hi]);
            lo <= k;
        }
    }
}
```

```expect
fail: `transport using` cannot narrow `loadable(v[lo..hi])` to `loadable(v[lo..k])`: narrowing a loadable range needs `k <= hi`, which is not an available fact
```
