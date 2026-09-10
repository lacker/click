# Abstract contract refinement unfolds predicates on both sides

An explicit theorem can compare two contracts whose state guarantees use
different named predicates. Each predicate definition must be opened before
the local refinement check.

```click
predicate IsZero(cell: int32[]) {
    cell[0] == 0
}

predicate IsNonnegative(cell: int32[]) {
    cell[0] >= 0
}

contract void ProducesZero(int32* cell) {
    owns cell[0..1];
    ensures IsZero(cell);
}

contract void ProducesNonnegative(int32* cell) {
    owns cell[0..1];
    ensures IsNonnegative(cell);
}

theorem zero_is_nonnegative(callback: void (*)(int32*)) {
    requires ProducesZero(callback);
    ensures ProducesNonnegative(callback) by {
        unfold(ProducesZero);
        unfold(ProducesNonnegative);
        unfold(IsZero);
        unfold(IsNonnegative);
        simp();
    }
}
```

```expect
pass
```
