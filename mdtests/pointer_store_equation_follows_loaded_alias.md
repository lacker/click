# Checked pointer stores feed same-state equality closure

A named resource supplies the loaded sibling alias. A store through that alias
establishes the same full pointer value at the original node name. No read
through the store spelling or explicit normalization is needed.

```c filename=link.c
struct node { uint64 tag; struct node *right; struct node *left; };
void link(struct node *p, struct node *q) {
    struct node *sibling = p->right;
    sibling->left = p;
}
```

```click
verifying "link.c";
resource links(p: struct node*, next: struct node*) {
    field model: int32;
    owns p->tag; owns p->right; owns p->left;
    fact p->right == next;
    fact p->left == 0;
}
void link(struct node* p, struct node* q) {
    consumes x: links(p, q);
    consumes y: links(q, 0);
    produces p->tag; produces p->right; produces p->left;
    produces q->tag; produces q->right; produces q->left;
    ensures q->left == p;
} by {
    unfold(x); unfold(y);
    step(); step(); step();
    have sibling == q;
    have q->left == p;
}
```

```expect
pass
```
