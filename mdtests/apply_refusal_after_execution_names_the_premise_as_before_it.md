# An `apply` refused after execution names its premise as before it

The companion of `apply_refusal_names_the_premise_a_removed_have_supplied.md`,
with the same `have` and `apply` written after
`step_until(function.exit)`. The function returns `n` so that execution needs
no premise of its own. The refusal is the same: it names the `apply`, the requirement as the lemma writes it, what its
parameter was bound to, and the fact it instantiates to.

```c filename=apply_refusal_after_execution_names_the_premise_as_before_it.c
int32 first(int32 *a, int32 n) {
    return n;
}
```

```click
verifying "apply_refusal_after_execution_names_the_premise_as_before_it.c";

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
    requires forall (k: int32) { 0 <= k and k < n implies a[k] >= 0 };
    ensures result >= 0;
} by {
    step_until(function.exit);
    have n >= 0;
    apply(head_nonnegative(a, n));
    close();
}
```

```expect
fail: `apply(head_nonnegative(a, n))` was refused: `first.contract` proof step tactic 2: theorem `head_nonnegative` has an unproved obligation: `0 < n`
```
