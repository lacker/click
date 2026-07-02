# symbolic pointer field load

This checks that Click can load an unknown pointer value from an external
struct field and use that loaded pointer as the base of a later write.

```c filename=write_stored_pointer.c
struct owner {
    int32* data;
};

int32 write_stored_pointer(struct owner* owner) {
    int32* current;
    current = owner->data;
    current[0] = 7;
    return current[0];
}
```

```click
verifying "write_stored_pointer.c";

int32 write_stored_pointer(struct owner* owner) {
    requires write(owner->data);
    requires write((owner->data)[0..1]);

    ensures result == 7 by auto;
}
```

```expect
pass
```
