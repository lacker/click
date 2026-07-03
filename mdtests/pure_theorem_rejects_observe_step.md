# pure theorem rejects resource observe step

This checks that theorem proof scripts cannot inspect the resource context.

```click
resource token(x: int32);

theorem observe_step_is_not_pure(x: int32) {
    ensures x == x by {
        observe(token(x));
        simp();
    }
}
```

```expect
fail: proof step `observe` cannot prove pure theorem `observe_step_is_not_pure`
```
