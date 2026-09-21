# the neighbouring `int32` field survives a store to this one

The struct-field half of the positive case. Two `int32` fields sit four bytes
apart, and each read is four bytes wide, so a store to one writes none of the
other's bytes. Separation by bytes has to keep this ordinary framing exactly
as cheap as separation by address was: the fields' addresses differ by a
constant, the constant clears the access, and nothing needs to be stated.

The refusal next door is `a_byte_store_inside_a_wide_cell_is_not_framed.md`,
where the same four-byte gap does *not* clear an eight-byte read.

```c filename=an_adjacent_int32_field_survives_a_neighbouring_store.c
struct pair {
    int32 first;
    int32 second;
};

int32 keep_second(struct pair* p) {
    p->first = 7;
    return p->second;
}
```

```click
verifying "an_adjacent_int32_field_survives_a_neighbouring_store.c";

int32 keep_second(struct pair* p) {
    consumes p->first;
    consumes p->second;

    ensures result == old(p->second);
    produces p->first;
    produces p->second;
} by {
    execute();
    simp();
}
```

```expect
pass
```
