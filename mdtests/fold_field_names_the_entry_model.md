# a fold field names the entry model of the instance it refolds

The positive side of
[`fold_field_names_a_consumed_model.md`](fold_field_names_a_consumed_model.md):
the initializer that refusal prints. `unfold(c)` consumed the instance, so the
`fold` names the field's value at function entry rather than at a state that
holds nothing.

```c filename=fold_field_names_the_entry_model.c
void touch(int32* p) {
    p[0] = 1;
}
```

```click
verifying "fold_field_names_the_entry_model.c";

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
    let c = fold(cell(p), { rank: old(c.rank) });
    simp();
}
```

```expect
pass
```
