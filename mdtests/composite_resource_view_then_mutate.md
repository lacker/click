# composite resource view then mutate

This checks that view-composite resource requirements project their immediate
contained views at function entry. The caller still observes its owned composite
before the call, then unfolds before the later mutation.

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
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 0 <= owner->cap;
    fact separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap]));
}

verifying "buffer_len.c";
verifying "len_then_clear.c";

int32 buffer_len(struct owner* owner) {
    views owned_buffer(owner);

    ensures result <= owner->cap by {
        execute();
        simp();
    }
}

int32 len_then_clear(struct owner* owner) {
    consumes owned_buffer(owner);

    produces owned_buffer(owner) by {
        observe(owned_buffer(owner));
        execute_until(statement(2));
        unfold(owned_buffer(owner));
        execute();
        have 0 <= owner->len by { simp(); }
        have owner->len <= owner->cap by { simp(); }
        have 0 <= owner->cap by { simp(); }
        have separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap])) by {
            simp();
        }
        fold(owned_buffer(owner));
    }
}
```

```expect
pass
```
