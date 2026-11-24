# A quantified implication cannot assume its own arithmetic domain

At `k == INT32_MAX`, the antecedent evaluates an overflowing sum. The old
lowering inserted a hidden definedness antecedent and let `intro` assume it.
Definedness is now an obligation, so the unchanged quantified claim must be
rejected before its proof introduces the written implication.

```click
theorem guarded_universal() {
    ensures forall (k: int32) {
        to_integer(k + 1) > 0 and k >= 0 implies k >= 0
    } by {
        intro();
        intro();
        intro();
        close();
    }
}
```

```expect
fail: not established: `forall
```
