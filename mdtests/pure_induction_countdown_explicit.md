# explicit induction certificate uses only checked operations

This is the fully expanded form of the smart proof in
`pure_induction_countdown.md`. The induction application names its exact side
conditions, and recursive evaluation is exposed by one-layer function
`unfold` operations.

```click
function countdown_explicit(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown_explicit(n - 1) }
}

theorem countdown_explicit_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown_explicit(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(countdown_explicit(n));
            normalize();
        } else {
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using {
                    0 < n;
                }
                assumption();
            }
            have n - 1 < n by {
                apply(int32_positive_predecessor_strictly_decreases(n)) using {
                    0 < n;
                }
                assumption();
            }
            apply(ih(n - 1)) using {
                0 <= n - 1;
                n - 1 < n;
                n - 1 >= 0;
            }
            unfold(countdown_explicit(n));
            assumption();
        }
    }
}
```

```expect
pass
```
