# Contract-to-contract refinement rejects wider ownership

The source contract owns both cells, while the target views both and owns only
the first. A theorem cannot narrow that ownership merely because both callbacks
carry the same C signature.

```click
contract void WideEffect(int32* cells) {
    owns cells[0..2];
}

contract void FirstCellEffect(int32* cells) {
    views cells[0..2];
    owns cells[0..1];
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
