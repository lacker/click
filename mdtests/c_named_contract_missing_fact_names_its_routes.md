# A missing concrete contract fact is absent, not refused

`Hooked` claims that `clear_cell` satisfies `SetsZero`, so folding it needs a
`SetsZero(&clear_cell)` fact. Nothing refused that claim here: `arm` simply
never established it. The diagnostic says the fact is absent and names the two
routes that establish it, instead of reporting the implementation as failing
the contract, which is what a refused refinement means.

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
} by {
    execute();
    simp();
}

void arm(int32* cell) {
    owns cell[0..1];
    produces Hooked(cell);
} by {
    execute();
    fold(Hooked(cell));
    simp();
}
```

```expect
fail: missing pure fact: no `SetsZero(&clear_cell)` fact is available; apply a refinement theorem or pass `&clear_cell` where `SetsZero` is required
```
