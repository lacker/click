# Integer pure functions accept ordinary and mathematical arguments

```click
function int_from_c(x: int32) -> Integer {
    to_integer(x)
}

function nat_to_integer_probe(n: Nat) -> Integer decreases n {
    match n {
        Nat::Zero => 0,
        Nat::Succ(k) => nat_to_integer_probe(k) + 1,
    }
}

theorem int_from_c_unfolds(x: int32) {
    ensures int_from_c(x) == to_integer(x) by {
        unfold(int_from_c(x));
        normalize();
    }
}

theorem nat_to_integer_zero_unfolds() {
    ensures nat_to_integer_probe(Nat::Zero) == 0 by {
        unfold(nat_to_integer_probe(Nat::Zero));
        normalize();
    }
}
```

```expect
pass
```
