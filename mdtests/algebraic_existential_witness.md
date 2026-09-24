# Algebraic existential witnesses and choices

The smallest proposition needed by the DFS reachability invariant is an
existential over `Nat`. A chosen algebraic witness remains usable as a field
of a later constructor witness.

```click
theorem nat_zero_exists() {
    ensures exists (fuel: Nat) { fuel == Nat::Zero } by {
        witness(fuel = Nat::Zero);
        normalize();
    }
}

theorem nat_successor_exists() {
    requires exists (fuel: Nat) { fuel == Nat::Zero };
    ensures exists (next: Nat) { next == Nat::Succ(Nat::Zero) } by {
        let (fuel: Nat) satisfy { fuel == Nat::Zero };
        witness(next = Nat::Succ(fuel));
        rewrite(fuel == Nat::Zero);
        normalize();
    }
}

theorem nat_reflexive_forall() {
    ensures forall (value: Nat) { value == value } by {
        intro();
        normalize();
    }
}
```

```expect
pass
```
