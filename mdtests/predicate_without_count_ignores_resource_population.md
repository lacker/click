# ordinary predicate identity ignores resource populations

A predicate that does not observe `count(...)` depends only on its explicit
arguments. Folding a composite resource may update Click's ghost population
ledger, but that unrelated transition must not change the identity of an
already-proved memory predicate needed by the resource body.

```c filename=predicate_without_count_ignores_resource_population.c
void wrap_zero(int32 *cell) {
}
```

```click
predicate is_zero(cell: int32*) {
    cell[0] == 0
}

resource zero_cell(cell: int32*) {
    owns cell[0..1];
    fact is_zero(cell);
}

verifying "predicate_without_count_ignores_resource_population.c";

void wrap_zero(int32* cell) {
    requires is_zero(cell);
    consumes cell[0..1];
    produces zero_cell(cell);
} by {
    fold(zero_cell(cell));
    execute();
    simp();
}
```

```expect
pass
```
