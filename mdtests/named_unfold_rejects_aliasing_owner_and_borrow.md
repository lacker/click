# A named owner's body cannot also be lent to its callee

Opening a named owner exposes its separation from checked incoming borrows.
The caller must not create such a partition by lending that same owner.

```c filename=probe.c
struct node { uint64 tag; };
void user(struct node *p, struct node *q) {}
void caller(struct node *p) { user(p, p); }
```

```click
verifying "probe.c";
resource owned(p: struct node*) { field model: int32; owns p->tag; }
void user(struct node* p, struct node* q) {
    consumes a: owned(p);
    produces p->tag;
    views q->tag;
    ensures separate(memory(p->tag), memory(q->tag));
} by {
    unfold(a);
    have separate(memory(p->tag), memory(q->tag)) by close();
}
void caller(struct node* p) {
    consumes a: owned(p);
    produces p->tag;
} by {
    let { model: m } = unfold(a);
    let a = fold(owned(p), { model: m });
    step();
}
```

```expect
fail: Borrowing this resource shape is unsupported.
```
