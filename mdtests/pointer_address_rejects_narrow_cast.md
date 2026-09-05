# A pointer does not fit a 32-bit integer

Under the LP64 profile a pointer is eight bytes wide. Casting it to a narrower
integer type is not a modeled conversion and is rejected.

```c filename=pointer_address_rejects_narrow_cast.c
struct node {
    int32 value;
    unsigned long word;
};

int32 truncate_pointer(struct node* node) {
    return (int32)node;
}
```

```click
verifying "pointer_address_rejects_narrow_cast.c";

int32 truncate_pointer(struct node* node) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer-to-integer cast requires a 64-bit integer type
```
