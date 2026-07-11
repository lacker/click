# owner buffer hidden writes imply folded separate

This checks that a folded composite resource exposes derived `separate(...)`
facts from its hidden contained `write(...)` permissions, while keeping the
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
    contains write(owner->len);
    contains write(owner->data);
    contains write((owner->data)[0..owner->len]);
    fact owner->len == 1;
}

verifying "observe_owner.c";

int32 observe_owner(struct owner* owner) {
    requires owned_buffer(owner);

    ensures separate(memory(owner[0..2]), memory((owner->data)[0..owner->len])) by auto;
}
```

```expect
pass
```
