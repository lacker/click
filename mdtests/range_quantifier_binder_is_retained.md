# A range quantifier's binder resolves through the retained binding

A range quantifier writes no `forall` node and no `implies` node: lowering
turns `(0..3).all(|k| body)` into a universal over `k` followed by the range
membership guard. `intro` learns both from the lowering record, so the written
name `k` is bound to the exact kernel variable the introduction created.

Every later mention of `k` resolves through that retained binding: the nested
`have` states a proposition about it, and `extract` cites one conjunct of the
range guard. Neither can reconstruct the binder from the theorem's parameters,
which never mention it.

```click
theorem range_binder_is_retained() {
    ensures (0..3).all(|k| { k < 3 }) by {
        intro();
        intro();
        have k < 3 by {
            extract(k < 3);
            assumption();
        }
        assumption();
    }
}
```

```expect
pass
```
