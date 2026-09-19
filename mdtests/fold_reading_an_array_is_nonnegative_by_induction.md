# a range fold whose body reads an array is proved by ordinary induction

The array-reading companion of
`mdtests/fold_function_is_nonnegative_by_induction.md`. The fold's body now
reads `v[k]`, so every step that writes a term naming the last cell also has to
place that cell inside a loadable range: the `have lo <= hi - 1` and
`have hi - 1 < n` here are what make `v[hi - 1]` a value the state holds, and
they are ordinary facts proved before the step that needs them.

The loadable range ends at the separate parameter `n`, not at `hi`, so the
hypothesis's loadability premise is the theorem's own, unchanged: `induct(hi)`
gives an induction hypothesis guarded by the theorem's own `requires` at the
smaller endpoint, and a range the induction does not move needs nothing proved
about it.

That is no longer the only way to write this theorem. A range ending at `hi`
makes `apply(ih(hi - 1))` demand `loadable(v[lo..hi - 1])` as an exact fact, and
that fact is now provable —
`mdtests/fold_reading_an_array_is_nonnegative_over_its_own_range.md` is the same
theorem over its own range. This version stays as the shape whose loadability
premise needs no proof at all.

```click
function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem unmarked_nonnegative(v: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n >= 0 and loadable(v[lo..n]);
    ensures 0 <= unmarked(v, lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            unfold(unmarked(v, lo, hi)) using {
                hi <= lo;
            }
            simp();
        } else {
            have lo < hi by { simp(); }
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= n by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; } }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
                hi - 1 <= n;
                n >= 0 and loadable(v[lo..n]);
                0 <= n - lo;
                n - lo <= 1073741823;
            }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < n by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; } }
            have hi - 1 < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; } }
            unfold(unmarked(v, lo, hi)) using {
                lo <= hi - 1;
                hi - 1 < 2147483647;
            }
            have 0 <= (if v[hi - 1] == 0 { 1 } else { 0 }) by { simp(); }
            apply(int32_less_equal_to_integer(0, if v[hi - 1] == 0 { 1 } else { 0 })) using {
                0 <= (if v[hi - 1] == 0 { 1 } else { 0 });
            }
            arithmetic_certificate {
                premise 0: 0 <= unmarked(v, lo, hi - 1) => 0 <= unmarked(v, lo, hi - 1);
                premise 1: to_integer(0) <= to_integer(if v[hi - 1] == 0 { 1 } else { 0 }) =>
                    0 <= to_integer(if v[hi - 1] == 0 { 1 } else { 0 });
                add 0, 1 =>
                    0 <= unmarked(v, lo, hi - 1) + to_integer(if v[hi - 1] == 0 { 1 } else { 0 });
                conclusion 2;
            }
        }
    }
}
```

```expect
pass
```
