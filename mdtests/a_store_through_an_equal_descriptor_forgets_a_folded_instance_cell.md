# A store through a descriptor proven equal forgets a folded instance's cell

The negative of `a_store_keeps_a_cell_a_folded_instance_owns.md` when the
two descriptors are one. The contract requires `s == other`: no caller can
lend both `object(other)` and an instance owning `object(s)` then, but the
entry check cannot see inside the folded instance, so the kernel must not
exploit it. A store opens a held instance's body only into a composition
that passes the check a flat context of the same ranges would, and with
`s == other` the opened `object(s)` overlaps the written `object(other)`, as
`owns object(s); owns object(other);` beside `requires s == other` is
refused. Nothing is opened, the store to `other->at` forgets the cached
`s->at`, and C's read of `s->at` is not the entry value.

```c filename=a_store_through_an_equal_descriptor_forgets_a_folded_instance_cell.c
struct slot {
    int32* data;
    int32 at;
    int32 end;
};

int32 touch(struct slot* s, struct slot* other) {
    other->at = 7;
    return s->at;
}
```

```click
resource slot_span(s: struct slot*) {
    field at: int32;
    field end: int32;
    owns object(s);
    fact s->at == at;
    fact s->end == end;
}

verifying "a_store_through_an_equal_descriptor_forgets_a_folded_instance_cell.c";

int32 touch(struct slot* s, struct slot* other) {
    requires s == other;
    owns r: slot_span(s);
    owns object(other);
    ensures result == old(s->at);
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == old(s->at)` failed
```
