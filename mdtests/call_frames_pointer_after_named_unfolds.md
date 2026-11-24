# Call frames pointer after named unfolds

An eight-byte pointer remains unchanged through two stores and a call after independent named unfolds. Four-byte cached loads are not partial writes.

```c filename=call_frames_pointer_after_named_unfolds.c
struct node { uint64 tag; struct node *right; struct node *left; };
void retarget(struct node *p, struct node *q, int32 *anchor) {}
void call(struct node *p, struct node *q, int32 *anchor) { p->right = 0; q->left = p; retarget(p, q, anchor); }
```

```click
verifying "call_frames_pointer_after_named_unfolds.c";
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
    mark before;
    let { b: c } = step(retarget, { a: c });
    have p->left == 0;
    unfold(c);
}
```

```expect
pass
```
