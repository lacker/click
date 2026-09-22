# An algebraic existential can carry a changing loop witness

The loop opens its algebraic existential invariant at iteration entry and
rebuilds it with a successor witness at the back edge. The C counter is only
the forcing loop; no verifier-only C state carries the ghost value.

```c filename=algebraic_existential_loop_witness.c
int32 count_to(int32 n) {
    int32 i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "algebraic_existential_loop_witness.c";

theorem nat_reflexive(value: Nat) {
    ensures value == value by { normalize(); }
}

int32 count_to(int32 n) diverges {
    requires 0 <= n;
    requires n < 2147483647;
    requires exists (fuel: Nat) { fuel == fuel };
    ensures result == result;
} by {
    step();
    step();
    loop diverges {
        invariant exists (fuel: Nat) { fuel == fuel };
        initialize by { simp(); }
        preserve by {
            step();
            choose(previous from invariant 0);
            apply(nat_reflexive(previous));
            have exists (fuel: Nat) { fuel == fuel } by {
                witness(fuel = Nat::Succ(previous));
                normalize();
            }
            close_invariants by { simp(); };
        }
    }
    execute();
    normalize();
}
```

```expect
pass
```
