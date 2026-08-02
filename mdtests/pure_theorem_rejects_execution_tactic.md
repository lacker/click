# pure theorem rejects C execution tactics

This checks that a pure proof cannot use execution tactics, which only make
sense when a C function claim supplies an execution frontier.

```click
theorem reflexive(x: int32) {
    ensures x == x by {
        execute();
        simp();
    }
}
```

```expect
fail: tactic `execute` is not available in the pure proof
```
