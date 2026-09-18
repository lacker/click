# a range fold over a symbolic range is proved by ordinary induction

This is the point of stating the fold laws over the function application. The
theorem is about a whole symbolic range, and its proof is the existing
`induct(hi)` over a nonnegative int32 parameter: the base case is the
empty-range equation, and the step case relates `marks(lo, hi)` to
`marks(lo, hi - 1)` — the very term the induction hypothesis speaks about,
because both sides of the append equation are the same function.

Nothing here retypes the fold, and no fold law is applied by name. The two
`unfold ... using` steps refresh the goal through the equation they open, so
the step case closes with the induction hypothesis and one bound on the cell
the last iteration adds.

```click
function marks(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if k == 0 { 1 } else { 0 }) })
}

theorem marks_nonnegative(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    ensures 0 <= marks(lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            unfold(marks(lo, hi)) using {
                hi <= lo;
            }
            simp();
        } else {
            have lo < hi by { simp(); }
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
            }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; } }
            unfold(marks(lo, hi)) using {
                lo <= hi - 1;
                hi - 1 < 2147483647;
            }
            have 0 <= (if hi - 1 == 0 { 1 } else { 0 }) by { simp(); }
            apply(int32_less_equal_to_integer(0, if hi - 1 == 0 { 1 } else { 0 })) using {
                0 <= (if hi - 1 == 0 { 1 } else { 0 });
            }
            arithmetic_certificate {
                premise 0: 0 <= marks(lo, hi - 1) => 0 <= marks(lo, hi - 1);
                premise 1: to_integer(0) <= to_integer(if hi - 1 == 0 { 1 } else { 0 }) =>
                    0 <= to_integer(if hi - 1 == 0 { 1 } else { 0 });
                add 0, 1 =>
                    0 <= marks(lo, hi - 1) + to_integer(if hi - 1 == 0 { 1 } else { 0 });
                conclusion 2;
            }
        }
    }
}
```

```expect
pass
```
