# a model field across a call that promises nothing about it

Returned ownership keeps its identity, not its old field values, so `bump` —
which says nothing about `rank` — leaves `caller` holding a fresh model. The
refusal used to end at `left side evaluated to v1000002`, two kernel variables
the reader had to guess at. It now spells the field, names the call that
replaced the model, and prints the clause that repairs it;
[`model_field_kept_by_a_call.md`](model_field_kept_by_a_call.md) is that clause
verifying.

```c filename=model_field_across_a_call_that_promises_nothing.c
void bump(int32* p) {
    p[0] = 1;
}

int32 caller(int32* p) {
    bump(p);
    return 0;
}
```

```click
verifying "model_field_across_a_call_that_promises_nothing.c";

resource cell(p: int32*) {
    field rank: int32;
    owns p[0..1];
}

void bump(int32* p) {
    owns c: cell(p);
} by {
    unfold(c);
    execute();
    let c = fold(cell(p), { rank: 0 });
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
fail: `c.rank` may have changed since function entry: the call to `bump` returned ownership of `c` with a new model, and `bump` promises nothing about this field. If it keeps the field, state `ensures c.rank == old(c.rank)` on `bump`.
```
