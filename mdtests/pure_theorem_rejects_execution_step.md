# pure theorem rejects C execution steps

This checks that pure theorem proofs do not accidentally use proof steps that
only make sense for C function claims.

```click
theorem reflexive(x: int32) {
    ensures x == x by {
        symbolic_execute();
        simp();
    }
}
```

```expect
fail: proof step `symbolic_execute` cannot prove pure theorem
```
