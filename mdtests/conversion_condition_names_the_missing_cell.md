# Logical conversion does not require a viewable cell

A logical read has a value even without a proved viewable extent. Its
reflexive equality needs no validity premise; actual C reads remain checked.

```click
theorem cell_from_range(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
}
```

```expect
pass
```
