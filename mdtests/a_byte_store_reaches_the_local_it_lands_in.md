# a byte store into a local is a write the local's own name sees

`a_byte_store_invalidates_the_wide_cell_it_covers.md` is this claim about an
`int64` reached through a parameter. Here the object is a stack local, and
that is a different route to the same read: a scalar local is held twice, as
the cell at its stack slot and as the binding a read of the *name* returns,
and a store through a pointer writes only the cell.

The binding was refreshed only where the store's address equalled the slot
exactly. `&v + 1` is not that address by any test — it is a different address
from `&v`, their offsets differ by a constant, they are not the same element
of any array — and the one byte written there is still the second byte of the
`int64` the name denotes. So the binding kept the whole value the assignment
put there, `return v` returned it, and `result == 5` was **provable** after a
store that made the result `0x0705`.

Which addresses reach a local is therefore a question about bytes, decided by
the same rule the store already applies to the cells it drops: a store that
covers the object completely, at its own address and in its own type, may
install its value; any other store that reaches those bytes leaves the binding
reading the slot out of the memory the store produced, which is what reading
the name means from then on.

The note on the C in `a_byte_store_inside_a_wide_cell_is_not_framed.md`
applies here too: what is pinned is the rule this store runs into, not an
endorsement of the byte view.

Since the little-endian byte view of integer cells landed (see
`docs/concepts/memory-model.md`), the store no longer drops the slot's cell:
it updates the `int64` cell at `&v` in place, so the refreshed binding reads
the exact value `0x0705 == 1797` rather than an unknown load of the slot. The
false claim `result == 5` is refuted by that value.

`write_through_the_whole_object` is the other polarity, and the reason the
rule is about bytes rather than about pointers at all: a store that covers the
object, at its own address and in its own type, still installs its value, so
the commonest write through a local's address costs nothing.

```c filename=a_byte_store_reaches_the_local_it_lands_in.c
int64 read_after_local_byte_write() {
    int64 v;
    unsigned char* b;
    v = 5;
    b = (unsigned char*)(void*) &v;
    b[1] = 7;
    return v;
}

int64 write_through_the_whole_object() {
    int64 v;
    int64* p;
    v = 5;
    p = &v;
    *p = 11;
    return v;
}
```

```click
verifying "a_byte_store_reaches_the_local_it_lands_in.c";

int64 read_after_local_byte_write() {
    ensures result == 5;
} by {
    execute();
    simp();
}

int64 write_through_the_whole_object() {
    ensures result == 11;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: result == 5; left side evaluated to 1797i64, right side evaluated to 5
```
