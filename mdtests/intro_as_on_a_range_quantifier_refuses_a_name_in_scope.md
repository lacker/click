# Named intro on a range quantifier refuses a name in scope

The name `let name = intro()` chooses must be new, for a range quantifier as for a
`forall`. `n` is the theorem's parameter, so it cannot also name the range's
variable.

```click
theorem range_scope(n: int32) {
    ensures (0..n).all(|k| { k < n }) by {
        let n = intro();
        intro();
        close();
    }
}
```

```expect
fail: `n` is already in scope here; choose a name that is not
```
