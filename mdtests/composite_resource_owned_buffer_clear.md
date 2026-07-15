# composite resource owned buffer clear

This checks a common mutation shape for a folded composite resource. Clearing
the length requires unfolding the owned buffer, executing the write, and folding
the resource back after re-establishing the len/cap facts.

```c filename=buffer_clear.c
struct owner {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_clear(struct owner* owner) {
    owner->len = 0;
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
    fact 0 <= owner->cap;
    fact separate(memory(owner[0..3]), memory((owner->data)[0..owner->cap]));
}

verifying "buffer_clear.c";

int32 buffer_clear(struct owner* owner) {
    consumes owned_buffer(owner);

    produces owned_buffer(owner) by {
        unfold(owned_buffer(owner));
        execute_rest();
        fold(owned_buffer(owner));
    }

    ensures result == 0 by {
        unfold(owned_buffer(owner));
        execute_rest();
        fold(owned_buffer(owner));
        simp();
    }
}
```

```expect
pass
```
