# Field-derived precise ownership survives metadata writes

`buffer_push` owns the whole buffer composite, writes only the old end cell,
its successor, and `owner->len`, and promises that the first cell is unchanged
when the old length is positive. The modular caller relies on that promise,
not on the callee's write footprint, to prove that `data[0]` survives the
call: a caller that only views a composite cannot see which of its cells a
callee owned.

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
    return index + 1;
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
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact separate(
        memory(owner[0..4]),
        memory(owner->data[0..owner->cap])
    );
}

int32 buffer_push(struct buffer* owner, int32 value) {
    requires 1 <= owner->len;
    requires owner->len + 1 < owner->cap;
    owns owned_buffer(owner);

    ensures result == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[0] == old(owner->data[0]);
} by {
    unfold(owned_buffer(owner));
    execute();
    have 0 <= owner->len by {
        simp();
    }
    have owner->len < owner->cap by {
        simp() using {
            old(owner->len) + 1 < old(owner->cap);
        }
    }
    fold(owned_buffer(owner));
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

    ensures data[0] == old(data[0]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
