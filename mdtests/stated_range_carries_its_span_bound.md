# applying a theorem owes its range premise's span bound

`viewable(p[lo..hi])` says two things: that `lo..hi` is a valid 32-bit byte
span, and that those bytes are viewable. A theorem that takes the range as a
premise gets both halves for free — see
[`have_viewable_prefix_of_a_range.md`](have_viewable_prefix_of_a_range.md),
which narrows a range without restating `hi - lo <= 1073741823`.

Both halves are owed on the other side of the same statement. This proof holds
`viewable(v[0..n])` at `n == 1 << 30`, which is true and says nothing — the
span `n * 4` wraps to zero bytes. Supplying it to a theorem whose premise is
a stated range would hand that theorem the valid-span fact it never
established, and the theorem would narrow zero bytes into a real cell. The
application is refused instead.

```click
theorem a_prefix_of_a_stated_range(v: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(v[lo..hi]);
    ensures viewable(v[lo..hi - 1]) by {
        have 0 < hi by { close() using { 0 <= lo; lo < hi; }; }
        have to_integer(lo) <= to_integer(hi - 1) by { close() using { lo < hi; 0 < hi; }; }
        have to_integer(hi - 1) < to_integer(hi) by { close() using { 0 < hi; }; }
        close();
    }
}

theorem a_wrapped_range_cannot_supply_it(v: int32[], n: int32) {
    requires n == 1073741824;
    ensures n >= 0 by {
        have 0 <= 0;
        have 0 < n by { close() using { n == 1073741824; }; }
        have n >= 0 by { close() using { n == 1073741824; }; }
        have n >= 0 and viewable(v[0..n]) by {
            have viewable(v[0..n]);
            close();
        }
        apply(a_prefix_of_a_stated_range(v, 0, n));
        close();
    }
}
```

```expect
fail: a memory range is too wide to be a 32-bit byte span
```
