# field-dependent owner buffer resource

This is the ergonomic owner-buffer shape where the resource only takes the
owner object, and the contained buffer permission is derived from `owner->data`
and `owner->len`. The resource packages the non-aliasing fact that the derived
buffer range does not overlap the owner fields.

```c filename=set_owned_first.c
struct owner {
    int32 len;
    int32* data;
};

int32 set_owned_first(struct owner* owner) {
    int32* current;
    current = owner->data;
    current[0] = owner->len;
    return current[0];
}
```

```click
resource owned_buffer(owner: struct owner*) {
    contains write(owner->len);
    contains write(owner->data);
    contains write((owner->data)[0..owner->len]);
    fact owner->len == 1;
    fact disjoint(owner[0..2], (owner->data)[0..owner->len]);
}

verifying "set_owned_first.c";

int32 set_owned_first(struct owner* owner) {
    requires owned_buffer(owner);

    ensures result == 1 by {
        unpack(owned_buffer(owner));
        symbolic_execute();
        pack(owned_buffer(owner));
        simp();
    }
}
```

```expect
pass
```
