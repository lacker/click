# field-dependent owner buffer resource

This is the more ergonomic owner-buffer shape we want eventually: the resource
only takes the owner object, and the contained buffer permission is derived
from `owner->data` and `owner->len`. Current Click cannot prove this yet because
the resource cannot yet package the needed non-aliasing fact between the owner
fields and the derived buffer range.

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
affine resource owned_buffer(owner: struct owner*) {
    contains write(owner->len);
    contains write(owner->data);
    contains write((owner->data)[0..owner->len]);
    fact owner->len == 1;
}

verifying "set_owned_first.c";

int32 set_owned_first(struct owner* owner) {
    requires owned_buffer(owner);

    ensures result == 1 by {
        open(owned_buffer(owner));
        symbolic_execute();
        close(owned_buffer(owner));
        simp();
    }
}
```

```expect
fail: fact failed
```
