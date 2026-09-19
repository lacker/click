# applying a theorem owes its range premise's extent bound

`loadable(p[lo..hi])` says two things: that `lo..hi` is a valid 32-bit byte
extent, and that those bytes are loadable. A theorem that takes the range as a
premise gets both halves for free — see
[`have_loadable_prefix_of_a_range.md`](have_loadable_prefix_of_a_range.md),
which narrows a range without restating `hi - lo <= 1073741823`.

Both halves are owed on the other side of the same statement. This proof holds
`loadable(v[0..n])` at `n == 1 << 30`, which is true and says nothing — the
extent `n * 4` wraps to zero bytes. Supplying it to a theorem whose premise is
a stated range would hand that theorem the valid-extent fact it never
established, and the theorem would narrow zero bytes into a real cell. The
application is refused instead.

```click
theorem a_prefix_of_a_stated_range(v: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and loadable(v[lo..hi]);
    ensures loadable(v[lo..hi - 1]) by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        simp();
    }
}

theorem a_wrapped_range_cannot_supply_it(v: int32[], n: int32) {
    requires n == 1073741824;
    ensures n >= 0 by {
        have 0 <= 0 by { simp(); }
        have 0 < n by { arithmetic() using { n == 1073741824; } }
        have n >= 0 by { arithmetic() using { n == 1073741824; } }
        have n >= 0 and loadable(v[0..n]) by {
            have loadable(v[0..n]) by { simp(); }
            split();
        }
        apply(a_prefix_of_a_stated_range(v, 0, n)) using {
            0 <= 0;
            0 < n;
            n >= 0 and loadable(v[0..n]);
        }
        assumption();
    }
}
```

```expect
fail: valid 32-bit byte extent here: `n <= 1073741823 is true` is not an available fact
```
