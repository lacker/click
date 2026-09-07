# An unfolded stateful predicate still requires a sufficient guarantee

Explicitly opening a predicate exposes its definition; it does not grant the
claim. A callback that promises only a nonnegative value does not establish
the strictly positive target predicate.

```c filename=weak_predicate_refinement.c
void choose_nonnegative(int32* cell) {
    cell[0] = 0;
}
```

```click
verifying "weak_predicate_refinement.c";

predicate IsPositive(cell: int32[]) {
    cell[0] > 0
}

contract void ProducesPositive(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
    ensures IsPositive(cell);
}

void choose_nonnegative(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
    ensures cell[0] >= 0;
} by {
    execute();
    frame();
    simp();
}

theorem nonnegative_is_positive() {
    ensures ProducesPositive(&choose_nonnegative) by {
        unfold(ProducesPositive);
        unfold(IsPositive);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `ProducesPositive(&choose_nonnegative)`
```
