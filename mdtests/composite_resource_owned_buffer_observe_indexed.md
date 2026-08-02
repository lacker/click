# composite resource owned buffer observe indexed

This checks that observing an owned buffer exposes enough immediate pure facts,
viewed contained resource facts, and deterministic loadability projections to
justify an indexed read through a field-dependent backing-array range.

```c filename=buffer_get.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_get(struct owner* owner, int32 index) {
    int32* data;
    data = owner->data;
    return data[index];
}
```

```click
resource owned_buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 0 <= owner->cap;
    fact separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap]));
}

verifying "buffer_get.c";

int32 buffer_get(struct owner* owner, int32 index) {
    consumes owned_buffer(owner);
    requires 0 <= index;
    requires index < owner->len;
    requires index < owner->cap;

    ensures result == (owner->data)[index] by {
        observe(owned_buffer(owner));
        execute();
        simp();
    }
}
```

```expect
pass
```
