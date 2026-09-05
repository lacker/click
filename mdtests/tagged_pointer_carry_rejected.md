# A tag that reaches the address bits is refuted

Adding 8 to an 8-byte-aligned address is not a tag: it changes an address
bit. Clearing the low three bits afterwards would not restore the pointer,
and the rewrite's obligation that the tag stays below the alignment is
refuted.

```c filename=tagged_pointer_carry_rejected.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* carry_into_address(struct node* next) {
    unsigned long word = (unsigned long)next + 8;
    return (struct node*)(word & ~7);
}
```

```click
verifying "tagged_pointer_carry_rejected.c";

struct node* carry_into_address(struct node* next) {
    requires aligned(next, 8);
    ensures result == next;
} by {
    execute();
    simp();
}
```

```expect
fail: clearing tag bits on a tagged pointer address needs the tag below 8, which is refuted
```
