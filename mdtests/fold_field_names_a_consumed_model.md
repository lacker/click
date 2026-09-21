# a fold field that reads the model its own `unfold` consumed

`unfold(c)` gives up the instance, so at the `fold` below it `c.rank` names no
model at all. The refusal used to be `fold field `rank`: the kernel evaluation
hit Paths` — a kernel budget enum in user text, naming no resource, no step and
no repair. It now names the field, says where the model still exists, and
prints the initializer that verifies: `{ rank: old(c.rank) }`, which is what
[`fold_field_names_the_entry_model.md`](fold_field_names_the_entry_model.md)
holds.

```c filename=fold_field_names_a_consumed_model.c
void touch(int32* p) {
    p[0] = 1;
}
```

```click
verifying "fold_field_names_a_consumed_model.c";

resource cell(p: int32*) {
    field rank: int32;
    owns p[0..1];
}

void touch(int32* p) {
    owns c: cell(p);
    ensures c.rank == old(c.rank);
} by {
    unfold(c);
    execute();
    let c = fold(cell(p), { rank: c.rank });
    simp();
}
```

```expect
fail: fold field `rank`: `c.rank` names no model here: `c` was consumed since function entry, so this state holds no field to read. Name the value it had there, `old(c.rank)`.
```
