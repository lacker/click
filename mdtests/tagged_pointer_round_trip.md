# A tag survives set, read, clear, and cast back

The `rb_node` shape: an aligned pointer becomes a word, a low bit is set, the
tag is read back through a mask, the tag is cleared, and the word converts
back to the original pointer, which can then be dereferenced. Every step is
an exact integer identity or a checked rewrite whose obligations follow from
the pointer's 8-byte alignment.

```c filename=tagged_pointer_round_trip.c
struct node {
    int32 value;
    unsigned long word;
};

int32 tag_round_trip(struct node* node, struct node* next) {
    unsigned long word = (unsigned long)next + 1;
    struct node* back = (struct node*)(word & ~3);
    node->word = word | 2;
    if ((word & 3) == 1) {
        return back->value;
    }
    return 0;
}
```

```click
verifying "tagged_pointer_round_trip.c";

int32 tag_round_trip(struct node* node, struct node* next) {
    requires node != 0;
    requires next != 0;
    requires aligned(next, 8);
    owns node->word;
    views next->value;
    mutable node->word;
    ensures result == next->value;
    ensures node->word == address(next) + 3;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
