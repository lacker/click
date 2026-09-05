# Tag operations need alignment evidence

Without knowing that the pointer's low bits are zero, masking the word may
alter an address bit, so the clearing rewrite leaves an unproved alignment
obligation and the postcondition cannot close.

```c filename=tagged_pointer_needs_alignment.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* clear_without_evidence(struct node* next) {
    unsigned long word = (unsigned long)next + 1;
    return (struct node*)(word & ~3);
}
```

```click
verifying "tagged_pointer_needs_alignment.c";

struct node* clear_without_evidence(struct node* next) {
    ensures result == next;
} by {
    execute();
    simp();
}
```

```expect
fail: clearing tag bits on a tagged pointer address needs the pointer aligned to 4 bytes
```
