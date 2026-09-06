# setting a bit at or above the alignment is rejected

A tag may occupy only bits the source pointer's alignment proves zero.
Setting bit 3 of a pointer only proven 8-aligned would change the address,
not a tag, so the operation needs 16-byte alignment that no evidence
provides; the proof fails promptly at that prerequisite instead of treating
the word as a tagged address.

```c filename=tagged_pointer_address_bit_rejected.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* set_address_bit(struct node* next) {
    unsigned long word = (unsigned long)next | 8;
    return (struct node*)(word & ~7);
}
```

```click
verifying "tagged_pointer_address_bit_rejected.c";

struct node* set_address_bit(struct node* next) {
    requires aligned(next, 8);
    ensures result == next;
} by {
    execute();
    simp();
}
```

```expect
fail: setting tag bits on a tagged pointer address needs the pointer aligned to 16 bytes
```
