# a viewable range with no established extent cannot be narrowed

Range narrowing reads an assumed `viewable(p[a..b])` as "the elements `a..b`".
That reading is only legitimate while the range's extent term, `(b - a) * width`
in 32-bit arithmetic, is the true count of bytes. At an element count of
`1 << 30` with four-byte elements the product is `1 << 32`, which is `0`: the
assumed fact then claims an empty extent, is vacuously true, and narrowing it
would turn nothing into a real cell.

So the rule asks for the range it starts from to be established as a valid
32-bit byte extent — the same side condition a contract carries — and refuses
when it is not. Every order fact is present here; only the extent is missing,
and the refusal says which two facts would supply it.

```click
theorem range_without_a_valid_extent(v: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(v[lo..hi]);
    ensures viewable(v[lo..hi - 1]) by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        extract(viewable(v[lo..hi]));
        transport(viewable(v[lo..hi]), viewable(v[lo..hi - 1])) using {
            viewable(v[lo..hi]);
            lo <= hi - 1;
            hi - 1 < hi;
        }
    }
}
```

```expect
fail: narrowing a viewable range needs `viewable(v[lo..hi])` established as a valid 32-bit byte extent, which takes `0 <= hi - lo` and an upper bound on `hi - lo` within the element count a 32-bit extent holds
```
