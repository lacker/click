# pure theorem rejects resource unpack step

This checks that theorem proof scripts cannot manipulate the resource context.

```click
affine resource token(x: int32);

theorem unpack_step_is_not_pure(x: int32) {
    ensures x == x by {
        unpack(token(x));
        simp();
    }
}
```

```expect
fail: proof step `unpack` cannot prove pure theorem `unpack_step_is_not_pure`
```
