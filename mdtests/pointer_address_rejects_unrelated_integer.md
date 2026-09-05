# An integer without pointer origin cannot become a pointer

Only a 64-bit value that is exactly a recorded pointer address, or zero, may
be cast back to a pointer type. An arbitrary `unsigned long` parameter has no
originating pointer, so the cast is rejected rather than manufacturing an
allocation identity.

```c filename=pointer_address_rejects_unrelated_integer.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* forge(unsigned long word) {
    return (struct node*)word;
}
```

```click
verifying "pointer_address_rejects_unrelated_integer.c";

struct node* forge(unsigned long word) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: integer-to-pointer cast requires a value that is a recorded pointer address or zero
```
