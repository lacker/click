# pure theorem rejects resource pack step

This checks that theorem proof scripts cannot manipulate the resource context.

```click
resource token(x: int32);

theorem pack_step_is_not_pure(x: int32) {
    ensures x == x by {
        pack(token(x));
        simp();
    }
}
```

```expect
fail: proof step `pack` cannot prove pure theorem `pack_step_is_not_pure`
```
