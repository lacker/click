# An antecedent cannot introduce an overflowing division as a fact

The quantified antecedent evaluates `n / k` when `k == -1`, where it
overflows for `n == -2147483648`. Retaining an antecedent must not turn its
undefined evaluation into an assumption. The right side of `and` is read only
where `k == -1`, so the division's domain is owed as
`k == -1 implies n != -2147483648 or k != -1`, which no premise establishes,
and the claim is rejected.

```c filename=retained_antecedent_survives_its_introduction.c
int32 retained_antecedent(int32 n) {
    return n;
}
```

```click
verifying "retained_antecedent_survives_its_introduction.c";

int32 retained_antecedent(int32 n) {
    ensures result == n;
} by {
    step();
    have forall (k: int32) { k == -1 and n / k == n implies n == n } by {
        intro();
        intro();
        have n / k == n;
        normalize();
    }
    close();
}
```

```expect
fail: not established: `forall
```
