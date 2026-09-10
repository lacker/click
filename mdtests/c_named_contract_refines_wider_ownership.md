# A named contract refines one that owns more

`FirstCellOwner` views both cells and owns only the first; `WideOwner` owns
both. A callback satisfying `FirstCellOwner` writes at most the first cell,
which every caller of `WideOwner` permits, and the wider owned range splits
into the view and the piece the callback needs. The refinement holds.

```click
contract void WideOwner(int32* cells) {
    owns cells[0..2];
}

contract void FirstCellOwner(int32* cells) {
    views cells[0..2];
    owns cells[0..1];
}

theorem first_cell_owner_is_wide_owner(
    callback: void (*)(int32*)
) {
    requires FirstCellOwner(callback);
    ensures WideOwner(callback) by {
        unfold(FirstCellOwner);
        unfold(WideOwner);
        simp();
    }
}
```

```expect
pass
```
