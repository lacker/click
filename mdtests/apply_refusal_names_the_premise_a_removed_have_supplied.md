# An `apply` whose premise a removed `have` supplied names that premise

`head_nonnegative` requires `0 < n`. The contract gives only `n >= 0`, and
the `have` states `n >= 0` again instead of the `0 < n` the lemma needs, so
the `apply` has no premise to cite and the implicit closer cannot prove one. This is the
shape a proof takes when the `have` that supplied the premise is removed or
restated.

The refusal used to blame the proof's shape: "It reached tactic 0 (nested
`have`), which is not implemented in this execution context", naming a
tactic that is not at fault and no premise at all. It now names the `apply`,
the requirement as the lemma writes it, what its parameter was bound to, and
the fact it instantiates to. State and prove that fact with `have` before the
application.

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
        have 0 <= 0 by normalize();
        instantiate(forall (k: int32) { 0 <= k and k < n implies a[k] >= 0 }, 0);
        close();
    }
}

int32 first(int32 *a, int32 n) {
    requires n >= 0;
    views a[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies a[k] >= 0 };
    ensures result >= 0;
} by {
    have n >= 0;
    apply(head_nonnegative(a, n));
}
```

```expect
fail: `apply(head_nonnegative(a, n))` was refused: `first.contract` proof step tactic 1: theorem `head_nonnegative` has an unproved obligation: `0 < n`
```
