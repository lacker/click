# A named contract does not refine one that owns less

`WideOwner` owns both cells; `FirstCellOwner` views both and owns only the
first. A callback satisfying `WideOwner` may write either cell, so it does not
satisfy `FirstCellOwner`: an implementation may own no more than the interface
it is claimed to refine. The refinement proof fails even after both contracts
are unfolded.

```click
contract void WideOwner(int32* cells) {
    owns cells[0..2];
}

contract void FirstCellOwner(int32* cells) {
    views cells[0..2];
    owns cells[0..1];
}

theorem wide_owner_is_first_cell_owner(
    callback: void (*)(int32*)
) {
    requires WideOwner(callback);
    ensures FirstCellOwner(callback) by {
        unfold(WideOwner);
        unfold(FirstCellOwner);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `FirstCellOwner(callback)`
```
