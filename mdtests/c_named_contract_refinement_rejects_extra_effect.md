# Contract-to-contract refinement rejects an extra mutable effect

The source contract may write either cell, while the target permits writes
only to the first. A theorem cannot erase that extra effect merely because
both callbacks carry the same resource and C signature.

```click
contract void WideEffect(int32* cells) {
    owns cells[0..2];
    mutable cells[0..2];
}

contract void FirstCellEffect(int32* cells) {
    owns cells[0..2];
    mutable cells[0..1];
}

theorem wide_effect_is_first_cell_effect(
    callback: void (*)(int32*)
) {
    requires WideEffect(callback);
    ensures FirstCellEffect(callback) by {
        unfold(WideEffect);
        unfold(FirstCellEffect);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `FirstCellEffect(callback)`
```
