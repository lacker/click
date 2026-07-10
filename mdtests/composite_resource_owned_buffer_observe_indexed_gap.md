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
    contains write(owner->len);
    contains write(owner->cap);
    contains write(owner->data);
    contains write((owner->data)[0..owner->cap]);
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 0 <= owner->cap;
    fact disjoint(owner[0..3], (owner->data)[0..owner->cap]);
}

verifying "buffer_get.c";

int32 buffer_get(struct owner* owner, int32 index) {
    requires owned_buffer(owner);
    requires 0 <= index;
    requires index < owner->len;
    requires index < owner->cap;

    ensures result == (owner->data)[index] by {
        observe(owned_buffer(owner));
        symbolic_execute();
        simp();
    }
}
```

```expect
pass
```
