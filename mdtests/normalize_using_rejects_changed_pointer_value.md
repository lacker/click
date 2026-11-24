# Recorded pointer normalization rejects a changed link

The second link is assigned null rather than the old parent pointer. The
normalizer must reject the claimed parent link even when the other copied
pointer and all framed resources remain valid.

```c filename=normalized_wrong_pointer_value.c
struct node { uint64 tag; struct node *right; struct node *left; };
void retarget(struct node *p, struct node *q, int32 *anchor) { q->tag = p->tag; p->tag = 1; }
void call(struct node *p, struct node *q, int32 *anchor) { p->right = q->left; q->left = 0; retarget(p, q, anchor); }
```

```click
verifying "normalized_wrong_pointer_value.c";
resource links(p: struct node*) {
    field model: int32;
    owns p->tag; owns p->left; owns p->right;
    fact p->left == 0;
}
resource cursor(p: struct node*, anchor: int32*) { field tag: int32; owns *anchor; }
void retarget(struct node* p, struct node* q, int32* anchor) {
    consumes a: cursor(p, anchor);
    owns p->tag;
    owns q->tag;
    produces b: cursor(q, anchor);
    ensures b.tag == old(a.tag);
    ensures q->tag == old(p->tag);
    ensures p->tag == 1;
} by {
    unfold(a);
    let b = fold(cursor(q, anchor), { tag: old(a.tag) });
}
void call(struct node* p, struct node* q, int32* anchor) {
    consumes c: cursor(p, anchor);
    consumes x: links(p);
    consumes y: links(q);
    produces p->tag; produces p->left; produces p->right;
    produces q->tag; produces q->left; produces q->right;
    produces *anchor;
    ensures p->left == 0;
} by {
    unfold(x); unfold(y);
    have separate(memory(p->left), memory(q->left)) by close();
    step(); step();
    have p->left == 0;
    have p->right == 0 by { close(); }
    mark before;
    let { b: c } = step(retarget, { a: c });
    have p->left == 0;
    have p->right == 0 by { normalize() using { at(before, p->right) == 0; }; }
    have q->left == p by { normalize() using { }; }
    unfold(c);
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
