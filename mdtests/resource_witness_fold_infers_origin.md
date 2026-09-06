# Folding infers the witness from the stored word

After storing a tail's address into the word, folding the resource binds the
witness to that tail without any explicit witness syntax: the `where` fact
names the word, and the word's recorded origin is the witness.

```c filename=resource_witness_fold_infers_origin.c
struct node {
    int32 value;
    unsigned long word;
};

void link(struct node* node, struct node* tail) {
    node->word = (unsigned long)tail;
}
```

```click
resource packed(node: struct node*) {
    owns object(node);
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}

verifying "resource_witness_fold_infers_origin.c";

void link(struct node* node, struct node* tail) {
    requires node != 0;
    requires aligned(tail, 8);
    consumes object(node);
    mutable node->word;
    produces packed(node);
} by {
    execute();
    frame();
    fold(packed(node));
    simp();
}
```

```expect
pass
```
