# a call that promises it keeps a model field

The positive side of
[`model_field_across_a_call_that_promises_nothing.md`](model_field_across_a_call_that_promises_nothing.md):
the clause that refusal prints. With `ensures c.rank == old(c.rank)` on `bump`,
the caller's field survives the call.

```c filename=model_field_kept_by_a_call.c
void bump(int32* p) {
    p[0] = 1;
}

int32 caller(int32* p) {
    bump(p);
    return 0;
}
```

```click
verifying "model_field_kept_by_a_call.c";

resource cell(p: int32*) {
    field rank: int32;
    owns p[0..1];
}

void bump(int32* p) {
    owns c: cell(p);
    ensures c.rank == old(c.rank);
} by {
    unfold(c);
    execute();
    let c = fold(cell(p), { rank: old(c.rank) });
    simp();
}

int32 caller(int32* p) {
    owns c: cell(p);
    requires c.rank == 3;
    ensures c.rank == 3;
} by {
    step(bump(p), { c: c });
    execute();
    simp();
}
```

```expect
pass
```
