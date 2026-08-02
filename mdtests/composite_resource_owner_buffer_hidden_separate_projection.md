# owner buffer hidden writes imply folded separate

This checks that a folded composite resource exposes derived `separate(...)`
facts from its hidden contained owned-memory permissions, while keeping the
permissions themselves hidden.

```c filename=observe_owner.c
struct owner {
    int32 len;
    int32* data;
};

int32 observe_owner(struct owner* owner) {
    return 0;
}
```

```click
resource owned_buffer(owner: struct owner*) {
    owns owner->len;
    owns owner->data;
    owns owner->data[0..owner->len];
    fact owner->len == 1;
}

verifying "observe_owner.c";

int32 observe_owner(struct owner* owner) {
    consumes owned_buffer(owner);

    ensures separate(memory(owner[0..2]), memory(owner->data[0..owner->len])) by auto;
}
```

```expect
pass
```
