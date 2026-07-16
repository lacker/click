# Field-derived precise effects survive metadata writes

This checks that a mutable footprint evaluated at function entry remains usable
after the function updates neighboring metadata. `buffer_push` writes only the
old end cell, its successor, and `owner->len`. The modular caller therefore
proves that the earlier `data[0]` cell is unchanged when the old length is
positive.

```c filename=field_derived_buffer_push.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push(struct buffer* owner, int32 value) {
    int32 index;
    index = owner->len;
    owner->data[index] = value;
    owner->len = index + 1;
    owner->data[index + 1] = 0;
    return owner->len;
}
```

```c filename=field_derived_buffer_push_preserves_first.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push_preserves_first(
    struct buffer* owner,
    int32 data[],
    int32 value
) {
    int32 ignored;
    ignored = buffer_push(owner, value);
    return ignored;
}
```

```click
verifying "field_derived_buffer_push.c";
verifying "field_derived_buffer_push_preserves_first.c";

resource owned_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact separate(
        memory(owner[0..4]),
        memory((owner->data)[0..owner->cap])
    );
}

int32 buffer_push(struct buffer* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_buffer(owner);
    mutable owner[0..1],
        (owner->data + owner->len)[0..2];

    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_buffer(owner));
    execute_rest();
    fold(owned_buffer(owner));
    frame();
    simp();
}

int32 buffer_push_preserves_first(
    struct buffer* owner,
    int32 data[],
    int32 value
) {
    requires 1 <= owner->len;
    requires owner->len + 1 < owner->cap;
    requires owner->data == data;
    owns owned_buffer(owner);
    mutable owner[0..1],
        (owner->data + owner->len)[0..2];

    ensures data[0] == old(data[0]);
} by {
    execute_rest();
    frame();
    simp();
}
```

```expect
pass
```
