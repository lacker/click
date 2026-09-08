# stdlib nat

```click
theorem nat_laws(a: Nat, b: Nat, c: Nat) {
    ensures nat_add(Nat::Zero, a) == a by { apply(nat_add_left_identity(a)); }
    ensures nat_add(a, Nat::Zero) == a by { apply(nat_add_right_identity(a)); }
    ensures nat_add(Nat::Succ(a), b) == Nat::Succ(nat_add(a, b)) by { apply(nat_add_succ_left(a, b)); }
    ensures nat_add(a, Nat::Succ(b)) == Nat::Succ(nat_add(a, b)) by { apply(nat_add_succ_right(a, b)); }
    ensures nat_add(nat_add(a, b), c) == nat_add(a, nat_add(b, c)) by { apply(nat_add_associative(a, b, c)); }
    ensures nat_add(a, b) == nat_add(b, a) by { apply(nat_add_commutative(a, b)); }
}

theorem one_plus_one() {
    ensures nat_add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero))
        == Nat::Succ(Nat::Succ(Nat::Zero)) by {
        unfold(nat_add(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero)));
        unfold(nat_add(Nat::Zero, Nat::Succ(Nat::Zero)));
        simp();
    }
}
```

```expect
pass
```
