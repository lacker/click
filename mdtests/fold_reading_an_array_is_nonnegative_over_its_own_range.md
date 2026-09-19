# a range fold over its own loadable range is proved by ordinary induction

`mdtests/fold_reading_an_array_is_nonnegative_by_induction.md` proves the same
theorem with the loadable range pinned to a separate parameter `n` that the
induction never moves. That was a workaround, and this is the shape it was
working around: the range ends at `hi`, the endpoint `induct(hi)` descends on,
so `apply(ih(hi - 1))` demands `loadable(v[lo..hi - 1])` as an exactly available
fact.

That fact is now provable, so the workaround is not needed. `induct(hi)` gives
an induction hypothesis guarded by the theorem's own `requires` at the smaller
endpoint; `have loadable(v[lo..hi - 1]) by { simp(); }` narrows the theorem's
own range to that endpoint, against the order facts proved just above it, and
`split()` assembles the hypothesis premise the guard is written as. Every other
step is unchanged from the version with `n`.

The theorem also carries `hi <= 1073741823`, which with `0 <= lo` bounds the
range's element count by the largest count a four-byte range can have and still
be a valid 32-bit byte extent. The induction hypothesis needs that bound at the
smaller endpoint like every other precondition, and the narrowing step needs the
count itself pinned to `0..=1073741823`, which the two `have`s state. This is a
real precondition of the shape, not bookkeeping: a range of `1 << 30` `int32`
elements has a byte extent of `1 << 32`, which wraps to `0`.

```click
function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem unmarked_nonnegative(v: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= 1073741823;
    requires hi >= 0 and loadable(v[lo..hi]);
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
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 >= 0 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have 0 <= hi - lo by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= 1073741823 by {
                arithmetic() using { 0 <= hi; hi <= 1073741823; }
            }
            have hi - lo <= 1073741823 by {
                arithmetic() using { 0 <= lo; lo < hi; hi <= 1073741823; }
            }
            have loadable(v[lo..hi - 1]) by { simp(); }
            have hi - 1 >= 0 and loadable(v[lo..hi - 1]) by { split(); }
            have 0 <= hi - 1 - lo by {
                arithmetic() using { 0 <= lo; lo < hi; hi <= 1073741823; }
            }
            have hi - 1 - lo <= 1073741823 by {
                arithmetic() using { 0 <= lo; lo < hi; hi <= 1073741823; }
            }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
                hi - 1 <= 1073741823;
                hi - 1 >= 0 and loadable(v[lo..hi - 1]);
                0 <= hi - 1 - lo;
                hi - 1 - lo <= 1073741823;
            }
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
