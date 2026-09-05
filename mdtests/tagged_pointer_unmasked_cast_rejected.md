# A tagged word does not convert back while its tag is set

Casting a word back without clearing a set tag bit would name a misaligned
address, so it is refuted rather than yielding the base pointer.

```c filename=tagged_pointer_unmasked_cast_rejected.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* forget_the_mask(struct node* next) {
    unsigned long word = (unsigned long)next + 1;
    return (struct node*)word;
}
```

```click
verifying "tagged_pointer_unmasked_cast_rejected.c";

struct node* forget_the_mask(struct node* next) {
    requires aligned(next, 8);
    ensures result == next;
} by {
    execute();
    simp();
}
```

```expect
fail: integer-to-pointer cast of a tagged address requires the tag bits proven zero; they are refuted
```
