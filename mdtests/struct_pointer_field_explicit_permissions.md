# struct pointer field with explicit permissions

This checks a struct that stores a pointer field and then writes through that
loaded pointer. The permissions are still explicit ranges: the struct range
covers the scalar field plus the pointer-sized field, and the buffer range
covers the cell written through the loaded pointer.

```c filename=set_owned_first.c
struct owner {
    int32 len;
    int32* data;
};

int32 set_owned_first(struct owner* owner, int32 data[]) {
    int32* current;
    owner->len = 1;
    owner->data = data;
    current = owner->data;
    current[0] = owner->len;
    return current[0];
}
```

```click
verifying "set_owned_first.c";

int32 set_owned_first(struct owner* owner, int32 data[]) {
    requires loadable(owner[0..3]);
    requires loadable(data[0..1]);
    consumes owner[0..3];
    consumes data[0..1];

    ensures result == 1 by auto;
    produces owner[0..3] by auto;
    produces data[0..1] by auto;
}
```

```expect
pass
```
