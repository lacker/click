# An algebraic induction binding remains in scope inside `have`

```click
function nat_id(n: Nat) -> Nat decreases n {
    match n {
        Nat::Zero => Nat::Zero,
        Nat::Succ(previous) => Nat::Succ(nat_id(previous)),
    }
}

function nat_zero(n: Nat) -> int32 decreases n {
    match n {
        Nat::Zero => 0,
        Nat::Succ(previous) => nat_zero(previous),
    }
}

theorem binding_in_have(n: Nat) {
    requires forall (k: int32) { k == k };
    ensures n == n by {
        induct(n) as ih {
            Nat::Zero => { normalize(); }
            Nat::Succ(previous) => {
                have previous == previous by { normalize(); }
                have nat_id(previous) == nat_id(previous) by { normalize(); }
                have 0 == 0 by {
                    instantiate(forall (k: int32) { k == k }, nat_zero(previous)) using {};
                    normalize();
                }
                normalize();
            }
        }
    }
}
```

```expect
pass
```
