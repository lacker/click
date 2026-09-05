# Address equality is pointer equality

Two address words compare equal exactly when their pointers do. A node whose
word holds its own address is self-parented; a node whose word holds a
distinct node's address is not. This is the `RB_EMPTY_NODE` shape.

```c filename=pointer_address_equality.c
struct node {
    int32 value;
    unsigned long word;
};

int32 self_after_clear(struct node* node) {
    node->word = (unsigned long)node;
    return node->word == (unsigned long)node;
}

int32 other_after_link(struct node* node, struct node* other) {
    node->word = (unsigned long)other;
    return node->word == (unsigned long)node;
}

int32 null_word_is_zero(struct node* node) {
    node->word = (unsigned long)0;
    return node->word == 0;
}
```

```click
verifying "pointer_address_equality.c";

int32 self_after_clear(struct node* node) {
    requires node != 0;
    owns node->word;
    mutable node->word;
    ensures result == 1;
} by {
    execute();
    frame();
    simp();
}

int32 other_after_link(struct node* node, struct node* other) {
    requires node != 0;
    requires other != node;
    owns node->word;
    mutable node->word;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

int32 null_word_is_zero(struct node* node) {
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
