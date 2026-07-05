# composite resource view call then mutate gap

This documents a remaining modular-call limitation. A caller can now pause
before the mutation, but function-call execution still runs the callee body with
only the callee's transferred resource summary. A helper that declares only
`views owned_buffer(owner)` does not yet get the observed contained memory views
needed to read `owner->len`.

```c filename=buffer_len.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_len(struct owner* owner) {
    return owner->len;
}
```

```c filename=len_then_clear.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 len_then_clear(struct owner* owner) {
    int32 old_len;
    old_len = buffer_len(owner);
    owner->len = 0;
    return old_len;
}
```

```click
resource owned_buffer(owner: struct owner*) {
    contains write(owner->len);
    contains write(owner->cap);
    contains write(owner->data);
    contains write((owner->data)[0..owner->cap]);
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 0 <= owner->cap;
    fact disjoint(owner[0..3], (owner->data)[0..owner->cap]);
}

verifying "buffer_len.c";
verifying "len_then_clear.c";

int32 buffer_len(struct owner* owner) {
    views owned_buffer(owner);

    ensures result <= owner->cap by {
        observe(owned_buffer(owner));
        execute_rest();
        simp();
    }
}

int32 len_then_clear(struct owner* owner) {
    requires owned_buffer(owner);

    ensures owned_buffer(owner) by {
        observe(owned_buffer(owner));
        execute_until(statement(2));
        unfold(owned_buffer(owner));
        execute_rest();
        fold(owned_buffer(owner));
    }
}
```

```expect
fail: MissingResource
```
