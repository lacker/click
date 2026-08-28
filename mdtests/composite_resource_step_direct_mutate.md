# composite resource execute step direct mutate

This checks statement-level execution boundaries. The proof executes the declaration
and read as separate steps while the buffer is folded, unfolds before the write,
then executes the write and return as separate steps before folding the buffer
back.

```c filename=len_then_clear_step.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 len_then_clear_step(struct owner* owner) {
    int32 old_len;
    old_len = owner->len;
    owner->len = 0;
    return old_len;
}
```

```click
resource owned_buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 0 <= owner->cap;
    fact separate(memory(owner[0..3]), memory(owner->data[0..owner->cap]));
}

verifying "len_then_clear_step.c";

int32 len_then_clear_step(struct owner* owner) {
    consumes owned_buffer(owner);

    produces owned_buffer(owner) by {
        observe(owned_buffer(owner));
        step();
        step();
        unfold(owned_buffer(owner));
        step();
        step();
        have 0 <= owner->len by simp;
        have owner->len <= owner->cap by simp;
        have 0 <= owner->cap by simp;
        have separate(memory(owner[0..3]), memory(owner->data[0..owner->cap])) by simp;
        fold(owned_buffer(owner));
    }
}
```

```expect
pass
```
