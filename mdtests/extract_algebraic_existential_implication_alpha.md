# An alpha-renamed existential is not extracted from a discharged implication

This differs from `extract_algebraic_existential_implication.md` only in the
bound variable's name. Both propositions mean the same thing. The antecedent
is also available exactly, and there is no C state or memory snapshot.

```click
theorem extract_algebraic_existential_alpha(flag: int32) {
    requires flag != 0;
    requires flag != 0 implies exists (callee_path: Nat) {
        callee_path == Nat::Zero
    };
    ensures exists (caller_path: Nat) {
        caller_path == Nat::Zero
    } by {
        extract(exists (caller_path: Nat) {
            caller_path == Nat::Zero
        });
        assumption();
    }
}
```

```expect
fail: `extract` proposition is not a proper conjunct
```
