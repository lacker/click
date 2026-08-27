# Smart frame ignores irrelevant snapshots

A contextual `frame()` should plan from the facts needed to cover the actual
write. Immutable calls can leave useful snapshots in the proof, but those
snapshots are not frame-certificate premises merely because they are ambient.

```c filename=inspect_buffer.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 inspect_buffer(struct buffer* owner) {
    return owner->len;
}
```

```c filename=write_after_calls.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 write_after_calls(struct buffer* owner, int32 index) {
    int32 value;
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    value = inspect_buffer(owner);
    owner->data[index] = value;
    return value;
}
```

```click
resource buffer_storage(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact loadable(owner->data[0..owner->len]);
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    );
}

verifying "inspect_buffer.c";
verifying "write_after_calls.c";

int32 inspect_buffer(struct buffer* owner) {
    views buffer_storage(owner);
    immutable;
    ensures result == owner->len;
} by {
    observe(buffer_storage(owner));
    execute();
    frame();
    simp();
}

int32 write_after_calls(struct buffer* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    owns buffer_storage(owner);
    mutable owner->data[index..index + 1];
    ensures result == owner->len;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    unfold(buffer_storage(owner));
    step();
    execute();
    frame();
    fold(buffer_storage(owner));
    simp();
}
```

```expect
pass
```
