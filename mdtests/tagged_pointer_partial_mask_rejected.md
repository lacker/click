# a mask that leaves a tag bit set is rejected

Clearing only the low bit of a word tagged with 3 would leave bit 1 set.
The clearing rule requires the whole tag below the cleared width, so the
mask itself is refuted rather than producing a word with a leftover tag.

```c filename=tagged_pointer_partial_mask_rejected.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* clear_one_of_two(struct node* next) {
    unsigned long word = (unsigned long)next + 3;
    return (struct node*)(word & ~1);
}
```

```click
verifying "tagged_pointer_partial_mask_rejected.c";

struct node* clear_one_of_two(struct node* next) {
    requires aligned(next, 8);
    ensures result == next;
} by {
    execute();
    simp();
}
```

```expect
fail: clearing tag bits on a tagged pointer address needs the tag below 2, which is refuted
```
