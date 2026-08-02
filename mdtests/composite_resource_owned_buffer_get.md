# composite resource owned buffer get first

This checks a read-only operation over the first cell of an owned buffer. The
value postcondition stays unfolded so it can mention the backing-array cell,
while the separate resource postcondition folds the buffer back.

```c filename=buffer_get_first.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_get_first(struct owner* owner) {
    int32* data;
    data = owner->data;
    return data[0];
}
```

```click
resource owned_buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..1];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact separate(memory(owner[0..3]), memory((owner->data)[0..1]));
}

verifying "buffer_get_first.c";

int32 buffer_get_first(struct owner* owner) {
    consumes owned_buffer(owner);
    ensures result == (owner->data)[0];
    produces owned_buffer(owner);
} by {
    unfold(owned_buffer(owner));
    execute();
    fold(owned_buffer(owner));
    simp();
}
```

```expect
pass
```
