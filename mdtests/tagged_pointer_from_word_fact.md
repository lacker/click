# A word known equal to a tagged address converts back

The callee never sees how `word` was formed; the contract states that it is
`next`'s address plus a tag. Clearing the tag bits and casting back recovers
`next`, and the tag reads back through the mask. This is `rb_parent` on a
word held in a local; the `next` parameter only carries the relation.

```c filename=tagged_pointer_from_word_fact.c
struct node {
    int32 value;
    unsigned long word;
};

int32 recovers_parent(unsigned long word, struct node* next) {
    return (struct node*)(word & ~3) == next;
}

int32 color_is_black(unsigned long word, struct node* next) {
    return (word & 1) == 1;
}
```

```click
verifying "tagged_pointer_from_word_fact.c";

int32 recovers_parent(unsigned long word, struct node* next) {
    requires aligned(next, 8);
    requires word == address(next) + 1;
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 color_is_black(unsigned long word, struct node* next) {
    requires aligned(next, 8);
    requires word == address(next) + 1;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
