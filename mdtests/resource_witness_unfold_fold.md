# A resource witness binds a packed pointer

A composite resource may bind an existential pointer with `let next: T
where P;`. On unfold the witness is a fresh symbolic pointer constrained by
`P`. The word below packs its numeric address with a low bit. Clearing the
bit recovers that address; this contract does not recover pointer bounds.

```c filename=resource_witness_unfold_fold.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* unpack(struct node* node) {
    return (struct node*)(node->word & ~1);
}
```

```click
resource packed(node: struct node*) {
    owns *node;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}

verifying "resource_witness_unfold_fold.c";

struct node* unpack(struct node* node) {
    requires node != 0;
    owns packed(node);
    ensures address(result) == (node->word & ~1);
} by {
    let { next: saved_next } = unfold(packed(node));
    step_until(function.exit);
    have address(result) == (node->word & ~1) by {
        close() using {
            aligned(result, 8);
            node->word == address(result) + (node->word & 1);
        }
    }
    fold(packed(node));
    close();
}
```

```expect
pass
```
