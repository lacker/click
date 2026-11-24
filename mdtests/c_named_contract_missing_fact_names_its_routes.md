# A missing concrete contract fact is absent, not refused

`Hooked` claims that `clear_cell` satisfies `SetsZero`, so folding it needs a
`SetsZero(&clear_cell)` fact. Nothing refused that claim here: `arm` simply
never established it. The diagnostic reports that exact unproved obligation;
it does not report a refused refinement of the implementation.

```c filename=named_contract_missing_fact.c
void clear_cell(int32* cell) {
    cell[0] = 0;
}

void arm(int32* cell) {
    cell[0] = 0;
}
```

```click
verifying "named_contract_missing_fact.c";

contract void SetsZero(int32* cell) {
    owns cell[0..1];
    ensures cell[0] == 0;
}

resource Hooked(cell: int32*) {
    owns cell[0..1];
    fact SetsZero(&clear_cell);
}

void clear_cell(int32* cell) {
    owns cell[0..1];
    ensures cell[0] == 0;
}

void arm(int32* cell) {
    owns cell[0..1];
    produces Hooked(cell);
} by {
    step_until(function.exit);
    fold(Hooked(cell));
    close();
}
```

```expect
fail: function `clear_cell` does not satisfy named contract `SetsZero` automatically
```
