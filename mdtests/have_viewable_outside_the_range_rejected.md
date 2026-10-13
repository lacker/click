# a `viewable` goal outside the assumed range is refused, by name

Range narrowing concludes `viewable(v[lo..k])` from `viewable(v[lo..hi])` only
when order facts place `[lo, k)` inside `[lo, hi)`. Here `lo <= k` is stated and
`k <= hi` is not, so the goal's upper end is not known to be inside the assumed
range and the step is refused.

The refusal identifies the checked transport that failed, with its source and
target. It does not infer a particular missing premise from the failed check.

```click
theorem range_not_inside_a_viewable_range(v: int32[], lo: int32, hi: int32, k: int32) {
    requires 0 <= lo;
    requires lo <= k;
    requires hi >= 0 and viewable(v[lo..hi]);
    ensures viewable(v[lo..k]) by {
        transport(viewable(v[lo..hi]), viewable(v[lo..k])) using {
            viewable(v[lo..hi]);
            lo <= k;
        }
    }
}
```

```expect
fail: `transport using` target does not follow from the source fact and the listed premises
```
