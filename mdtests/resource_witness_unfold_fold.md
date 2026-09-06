# A resource witness binds a packed pointer

A composite resource may bind an existential pointer with `let next: T
where P;`. On unfold the witness is a fresh symbolic pointer constrained by
`P`; on fold it is the recorded origin of the word `P` relates it to. The
word below packs the witness's address with a low bit, and clearing the bit
recovers exactly the witness.

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
    owns object(node);
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}

verifying "resource_witness_unfold_fold.c";

struct node* unpack(struct node* node) {
    requires node != 0;
    owns packed(node);
    ensures address(result) == (node->word & ~1);
} by {
    unfold(packed(node));
    execute();
    fold(packed(node));
    simp();
}
```

```expect
pass
```
