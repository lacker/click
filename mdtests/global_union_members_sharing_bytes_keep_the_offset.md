# Union members that share bytes keep the cell's byte offset

The counterpart of `a_global_struct_field_store_names_the_field.md`. The four
bytes at offset 4 of `g` are both `g.bits.signed_view` and
`g.bits.other_view`, so no one field name is exactly the cell the loop
writes, and the memory-history sentence keeps the offset `g+4`.

```c filename=global_union_members_sharing_bytes_keep_the_offset.c
union bits {
    int32 signed_view;
    int32 other_view;
};

struct packet {
    int32 tag;
    union bits bits;
};

struct packet g;

int32 loop_writes_member() {
    int32* p;
    int32 i;
    p = &g.bits.signed_view;
    i = 0;
    while (i < 2) {
        p[0] = 9;
        i = i + 1;
    }
    return g.bits.signed_view;
}
```

```click
verifying "global_union_members_sharing_bytes_keep_the_offset.c";

int32 loop_writes_member() {
    owns g.tag;
    owns g.bits.signed_view;
    requires g.bits.signed_view == 3;
    ensures result == 3;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    execute();
    simp();
}
```

```expect
fail: right side evaluated to 3; `g+4` may have changed since earlier in this function
```
