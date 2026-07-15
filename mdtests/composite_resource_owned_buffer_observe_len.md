# composite resource owned buffer observe len

This checks that `observe(resource)` is enough to use the immediate viewed
facts and read permissions of a folded len/cap/data buffer resource without
unfolding the owned permissions.

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

```click
resource owned_buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap]));
}

verifying "buffer_len.c";

int32 buffer_len(struct owner* owner) {
    consumes owned_buffer(owner);

    ensures result <= owner->cap by {
        observe(owned_buffer(owner));
        symbolic_execute();
        simp();
    }

    produces owned_buffer(owner) by {
        observe(owned_buffer(owner));
        symbolic_execute();
    }
}
```

```expect
pass
```
