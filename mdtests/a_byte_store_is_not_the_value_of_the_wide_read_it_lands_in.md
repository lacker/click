# a byte store is not the value of the wide read it lands in

`b[1] = 7` writes the second byte of the `int32` at `q`. The read `*q` that
follows returns all four bytes: the old low byte, `7` in the second, and the
old upper half. Nothing makes it `7`.

That read was **provable** as `7`. The cell walk that names `*q` stops at the
byte store, correctly, because the store writes a byte the read returns. It
then reported the store's value as the value the read pins down, and the
check of `need7`'s precondition resolves each load through that answer, so
`d == 7` became `7 == 7`. A store that only reaches a read's bytes is not
the read's value. Click has no rule that extracts a narrower read from a
wider store or assembles a wider read from a narrower one, so a stored value
answers for a read only when the store starts at the read's address and is
exactly as wide.

`a_byte_store_is_not_the_value_of_an_int16_read.md` is the same claim about
an `int16`, and
`two_byte_stores_do_not_make_two_wide_reads_equal.md` is the claim about two
reads that each stop at such a store.

The note on the C in `a_byte_store_inside_a_wide_cell_is_not_framed.md`
applies here too: what is pinned is the rule this store runs into, not an
endorsement of the byte view.

```c filename=a_byte_store_is_not_the_value_of_the_wide_read_it_lands_in.c
int32 need7(int32 x) {
    return x - 7;
}

int32 caller(int32* q) {
    unsigned char* b;
    int32 d;
    b = (unsigned char*)(void*) q;
    b[1] = 7;
    d = *q;
    return need7(d);
}
```

```click
verifying "a_byte_store_is_not_the_value_of_the_wide_read_it_lands_in.c";

int32 need7(int32 x) {
    requires x == 7;
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller(int32* q) {
    owns q[0..1];
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: missing prerequisite (precondition clause 1 of `need7`)
```
