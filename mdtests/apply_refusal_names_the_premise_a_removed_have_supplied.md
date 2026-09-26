# An `apply` whose premise a removed `have` supplied names that premise

`head_nonnegative` requires `0 < n`. The contract gives `n > 1`, and the
`have` states `n > 1` again instead of the `0 < n` the lemma needs, so the
`apply` has no exact premise to cite. This is the shape a proof takes when the
`have` that supplied the premise is removed or restated.

The refusal used to blame the proof's shape: "It reached tactic 0 (nested
`have`), which is not implemented in this execution context", naming a
tactic that is not at fault and no premise at all. It now names the `apply`,
the requirement as the lemma writes it, what its parameter was bound to, and
the fact it instantiates to.

```c filename=apply_refusal_names_the_premise_a_removed_have_supplied.c
int32 first(int32 *a, int32 n) {
    return a[0];
}
```

```click
verifying "apply_refusal_names_the_premise_a_removed_have_supplied.c";

theorem head_nonnegative(a: int32[], n: int32) {
    requires 0 < n;
    requires forall (k: int32) { 0 <= k and k < n implies a[k] >= 0 };
    ensures a[0] >= 0 by {
        have 0 <= 0 by { normalize(); }
        instantiate(forall (k: int32) { 0 <= k and k < n implies a[k] >= 0 }, 0) using {
            0 <= 0;
            0 < n;
        }
        assumption();
    }
}

int32 first(int32 *a, int32 n) {
    requires n > 1;
    views a[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies a[k] >= 0 };
    ensures result >= 0;
} by {
    have n > 1 by { simp(); }
    apply(head_nonnegative(a, n));
    execute();
    simp();
}
```

```expect
fail: `apply(head_nonnegative(a, n))` was refused: `first.contract` proof step tactic 1: required exact fact for theorem `head_nonnegative` is unavailable: requirement 1 `0 < n` with n = n instantiates to `0 < n`
```
