# a `viewable` goal outside the assumed range is refused, by name

Range narrowing concludes `viewable(v[lo..k])` from `viewable(v[lo..hi])` only
when order facts place `[lo, k)` inside `[lo, hi)`. Here `lo <= k` is stated and
`k <= hi` is not, so the goal's upper end is not known to be inside the assumed
range and the step is refused.

The refusal names the missing fact in the spelling the theorem uses, because
that is what the reader has to prove next. It does not print two lowered byte
extents and leave the arithmetic to them.

```click
theorem range_not_inside_a_viewable_range(v: int32[], lo: int32, hi: int32, k: int32) {
    requires 0 <= lo;
    requires lo <= k;
    requires hi >= 0 and viewable(v[lo..hi]);
    ensures viewable(v[lo..k]) by {
        extract(viewable(v[lo..hi]));
        transport(viewable(v[lo..hi]), viewable(v[lo..k])) using {
            viewable(v[lo..hi]);
            lo <= k;
        }
    }
}
```

```expect
fail: `transport using` cannot narrow `viewable(v[lo..hi])` to `viewable(v[lo..k])`: narrowing a viewable range needs `k <= hi`, which is not an available fact
```
