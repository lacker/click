# Composite unfold ignores unrelated snapshots

Unfolding a small composite resource is a simple tactic. Earlier immutable
calls may leave useful program points in the proof, but they must not make the
resource projection repeatedly normalize the complete snapshot history.

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

```c filename=read_after_calls.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 read_after_calls(struct buffer* owner) {
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

resource allocated_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    contains allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact owner->cap <= 536870911;
    fact loadable(owner->data[0..owner->len]);
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    );
}

verifying "inspect_buffer.c";
verifying "read_after_calls.c";

int32 inspect_buffer(struct buffer* owner) {
    views buffer_storage(owner);
    immutable;
    ensures result == owner->len;
    ensures forall (k: int32) {
        0 <= k and k < owner->len implies
            owner->data[k] == old(owner->data[k])
    };
} by {
    observe(buffer_storage(owner));
    execute();
    frame();
    simp();
}

int32 read_after_calls(struct buffer* owner) {
    owns allocated_buffer(owner);
    immutable;
    ensures result == owner->len;
} by {
    unfold(allocated_buffer(owner));
    fold(buffer_storage(owner));
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
    have 0 <= owner->len by simp;
    have owner->len <= owner->cap by simp;
    have 1 <= owner->cap by simp;
    have owner->cap <= 536870911 by simp;
    execute();
    frame();
    fold(allocated_buffer(owner));
    simp();
}
```

```expect
pass
```
