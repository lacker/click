# Closing a resource population body requires restoring it

`open` does not permit a proof to destroy part of a population body and then
retain the folded population resource.

```c filename=use_population.c
int32 use_population(int32* cell) {
    return 0;
}
```

```click
resource inner_cell(cell: int32*) {
    owns cell[0..1];
}

resource population(cell: int32*) {
    owns cell[0..1];
}

verifying "use_population.c";

int32 use_population(int32* cell) {
    owns population(cell);
} by {
    open(population(cell)) {
        fold(inner_cell(cell));
    }
    execute();
}
```

```expect
fail: closing `open(population(cell))`
```
