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
    requires valid_range(owner[0..3]);
    requires valid_range(data[0..1]);
    requires write(owner[0..3]);
    requires write(data[0..1]);

    ensures result == 1 by auto;
    ensures write(owner[0..3]) by auto;
    ensures write(data[0..1]) by auto;
}
```

```expect
pass
```
