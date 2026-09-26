# A store forgets a cell of a matched folded instance

The negative of `a_store_keeps_a_cell_a_folded_instance_owns.md` for a
matched body. Both arms of `maybe_slot(s)` own `object(s)`, so `s->at` is
readable at entry and the claim is true, but the arm is not decided. A store
opens a held instance one body layer only when the body is unconditional and
unmatched, exactly as the call havoc's kept-by-caller rule does: a matched
body, decided or not, is not opened, so the store to `other->at` forgets
`s->at` and the postcondition cannot read the entry value.

```c filename=a_store_forgets_a_cell_of_a_matched_folded_instance.c
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
spec enum Phase {
    Idle,
    Busy,
}

resource maybe_slot(s: struct slot*) {
    field phase: Phase;
    match phase {
        Phase::Idle => {
            owns object(s);
        },
        Phase::Busy => {
            owns object(s);
        },
    }
}

verifying "a_store_forgets_a_cell_of_a_matched_folded_instance.c";

void touch(struct slot* s, struct slot* other) {
    owns r: maybe_slot(s);
    owns object(other);
    requires s->at == 5;
    ensures s->at == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures s->at == 5` failed
```
