# composite resource owned buffer observe indexed gap

This documents the current gap for dependent contained resource facts.
Observing an owned buffer exposes immediate pure facts and viewed contained
resource facts, but this proof path does not yet make the field-dependent
backing-array range usable as the pure `CMemoryLoadable` fact needed for the
indexed load.

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
fail: missing pure fact: loadable
```
