# A range quantifier's binder resolves through the retained binding

A range quantifier writes no `forall` node and no `implies` node: lowering
turns `(0..3).all(|k| body)` into a universal over `k` followed by the range
membership guard. `intro` learns both from the lowering record, so the written
name `k` is bound to the exact kernel variable the introduction created and a
later `extract` that names `k` resolves through that retained binding.

```click
theorem range_binder_is_retained() {
    ensures (0..3).all(|k| { k < 3 }) by {
        intro();
        intro();
        extract(k < 3);
        assumption();
    }
}
```

```expect
pass
```
