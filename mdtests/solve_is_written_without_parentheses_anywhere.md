# solve is written the same way anywhere

`close();` is written the same way as a block's only step and after a `have`,
with or without a `using` list.

```click
theorem bare_solve_steps(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        close();
    }
    ensures 0 <= x by {
        have 0 <= x by { close() using { 0 <= x; }; }
        close();
    }
}
```

```expect
pass
```
