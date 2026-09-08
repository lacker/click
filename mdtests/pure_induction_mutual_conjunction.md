# one strong hypothesis can carry a mutual recursive property

Mutually recursive pure functions do not require a separate mutually
inductive theorem group when one proposition states the joint property.

```click
function parity_even(n: int32) -> int32
    decreases n
{
    if n <= 0 { 1 } else { parity_odd(n - 1) }
}

function parity_odd(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { parity_even(n - 1) }
}

theorem parity_is_complementary(n: int32) {
    requires n >= 0;
    ensures parity_even(n) + parity_odd(n) == 1 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(parity_even(n));
            unfold(parity_odd(n));
            normalize() using { n <= 0; }
        } else {
            have parity_even(n) == parity_odd(n - 1) by {
                unfold(parity_even(n));
                normalize() using { not(n <= 0); }
            }
            have parity_odd(n) == parity_even(n - 1) by {
                unfold(parity_odd(n));
                normalize() using { not(n <= 0); }
            }
            rewrite(parity_even(n) == parity_odd(n - 1));
            rewrite(parity_odd(n) == parity_even(n - 1));
            have parity_odd(n - 1) + parity_even(n - 1)
                == parity_even(n - 1) + parity_odd(n - 1) by {
                normalize();
            }
            rewrite(parity_odd(n - 1) + parity_even(n - 1)
                == parity_even(n - 1) + parity_odd(n - 1));
            apply(ih(n - 1));
            assumption();
        }
    }
}
```

```expect
pass
```
