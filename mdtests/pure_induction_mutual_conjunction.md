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
            simp();
        } else {
            if n <= 1 {
                if n - 1 <= 0 {
                    simp();
                } else {
                    simp();
                }
            } else {
                if n - 1 <= 0 {
                    simp();
                } else {
                    apply(ih((n - 1) - 1));
                    simp();
                }
            }
        }
    }
}
```

```expect
pass
```
