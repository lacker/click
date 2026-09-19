# a range fold over its own viewed range is proved by ordinary induction

`mdtests/fold_reading_an_array_is_nonnegative_over_its_own_range.md` proves this
theorem with the range stated as `requires hi >= 0 and loadable(v[lo..hi]);`.
That conjunction was not a style choice: a bare `requires loadable(...)` did not
compile in a theorem, so the range had to ride inside a proposition. `views
v[lo..hi];` states the same hypothesis directly, and this file is the same proof
with that one clause changed. The original stays as the regression for the
spelling that still exists.

Two lines disappear with the conjunction. The hypothesis premise is now the
range itself, so `apply(ih(hi - 1))` names it as `loadable(v[lo..hi - 1])` —
the fact form, which is how a `views` premise is named in a `using` list —
instead of rebuilding `hi - 1 >= 0 and loadable(v[lo..hi - 1])` with `split()`.

Everything else is unchanged, including why the extent facts are there. The
theorem carries `hi <= 1073741823`, which with `0 <= lo` bounds the range's
element count by the largest count a four-byte range can have and still be a
valid 32-bit byte extent. The induction hypothesis owes that bound at the
smaller endpoint like every other precondition, and the narrowing step needs the
count itself pinned to `0..=1073741823`, which the two `have`s state.

```click
function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem unmarked_nonnegative(v: int32[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= 1073741823;
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
            have 0 <= hi - lo by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= 1073741823 by {
                arithmetic() using { 0 <= hi; hi <= 1073741823; }
            }
            have hi - lo <= 1073741823 by {
                arithmetic() using { 0 <= lo; lo < hi; hi <= 1073741823; }
            }
            have loadable(v[lo..hi - 1]) by { simp(); }
            have 0 <= hi - 1 - lo by {
                arithmetic() using { 0 <= lo; lo < hi; hi <= 1073741823; }
            }
            have hi - 1 - lo <= 1073741823 by {
                arithmetic() using { 0 <= lo; lo < hi; hi <= 1073741823; }
            }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                loadable(v[lo..hi - 1]);
                0 <= lo;
                hi - 1 <= 1073741823;
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
