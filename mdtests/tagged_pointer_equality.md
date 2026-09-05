# Tagged words compare by pointer and tag

`RB_EMPTY_NODE` compares a node's word with its own address. With the tag
structure known, the comparison is decided: the same pointer with a
different tag is unequal, and distinct aligned nodes with small tags cannot
produce the same word.

```c filename=tagged_pointer_equality.c
struct node {
    int32 value;
    unsigned long word;
};

int32 self_with_tag(struct node* node) {
    node->word = (unsigned long)node + 1;
    return node->word == (unsigned long)node;
}

int32 other_with_tag(struct node* node, struct node* other) {
    node->word = (unsigned long)other + 1;
    return node->word == (unsigned long)node;
}

int32 same_word(struct node* node, struct node* other) {
    node->word = (unsigned long)other + 1;
    return node->word == (unsigned long)other + 1;
}
```

```click
verifying "tagged_pointer_equality.c";

int32 self_with_tag(struct node* node) {
    requires node != 0;
    owns node->word;
    mutable node->word;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

int32 other_with_tag(struct node* node, struct node* other) {
    requires node != 0;
    requires other != node;
    requires aligned(node, 8);
    requires aligned(other, 8);
    owns node->word;
    mutable node->word;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

int32 same_word(struct node* node, struct node* other) {
    requires node != 0;
    owns node->word;
    mutable node->word;
    ensures result == 1;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
