# pure theorem rejects C execution steps

This checks that a pure proof cannot use execution proof steps, which only make
sense when a C function claim supplies an execution frontier.

```click
theorem reflexive(x: int32) {
    ensures x == x by {
        symbolic_execute();
        simp();
    }
}
```

```expect
fail: proof step `symbolic_execute` is not available in the pure proof
```
