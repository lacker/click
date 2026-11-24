# An `obtain` binds its own name and nothing else

Putting an obtained witness in scope for later tactics does not make other
names resolve: a proposition naming a variable nothing bound is still refused
as unbound.

```click
theorem ob(x: int32) {
    requires exists (k: int32) { k > x };
    ensures 0 == 1 by {
        let k = obtain(exists (k: int32) { k > x });
        have z > x by close();
    }
}
```

```expect
fail: unbound variable `z`
```
