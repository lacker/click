# A store keeps a cell a folded instance owns

`touch` owns the descriptor `object(s)` only inside the folded field-bearing
instance `r`, and writes `other->at` through its flat `object(other)`. The
cells of `r`'s unconditional, unmatched body are named at entry, where the
precondition reads `s->at`, and the store keeps `s->at`: the instance is held
here, its body owns `object(s)` one layer down, and that is a different owned
member than the one holding the written bytes, so the partition law places
the two apart exactly as it does for two flat members. The postcondition
reads the entry value without unfolding `r`.

The negatives are `a_store_forgets_a_cell_of_a_matched_folded_instance.md`
(a matched body is not opened) and
`a_store_through_an_equal_descriptor_forgets_a_folded_instance_cell.md` (the
addresses are proven equal).

```c filename=a_store_keeps_a_cell_a_folded_instance_owns.c
struct slot {
    int32* data;
    int32 at;
    int32 end;
};

void touch(struct slot* s, struct slot* other) {
    other->at = 7;
}
```

```click
resource slot_span(s: struct slot*) {
    field at: int32;
    owns object(s);
    fact s->at == at;
}

verifying "a_store_keeps_a_cell_a_folded_instance_owns.c";

void touch(struct slot* s, struct slot* other) {
    owns r: slot_span(s);
    owns object(other);
    requires s->at == 5;
    ensures s->at == 5;
} by {
    execute();
    simp();
}
```

```expect
pass
```
