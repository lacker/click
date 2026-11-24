# A saved pointer link retains its bounds after its outer alias changes

The saved full pointer value remains usable after `root->left` is overwritten.
Unfolding adjacent fields must not replace its eight-byte read domain with a
four-byte cache prefix.

```c filename=probe.c
struct node { unsigned long tag; struct node *right; struct node *left; };
void put(struct node *p, struct node *q) { p->right = q; }
void caller(struct node *root, struct node *p, struct node *q) { root->left = q; put(p, q); }
```

```click
verifying "probe.c";
spec enum Link { Link(void*), }
resource saved(slot: struct node**) {
    field model: Link;
    match model { Link::Link(child) => { owns *slot; fact *slot == child; }, }
}
resource right_link(p: struct node*, q: struct node*) {
    owns p->right;
    fact p->right == q;
}
void put(struct node *p, struct node *q) {
    owns p->right;
    ensures p->right == q;
}
void caller(struct node *root, struct node *p, struct node *q) {
    owns root->left;
    requires root->left == p;
    owns p->left;
    owns p->right;
    ensures p->left == old(root->left->left);
} by {
    let s = fold(saved(&p->left), { model: Link::Link(p->left) });
    step();
    step();
    fold(right_link(p, q));
    unfold(s);
    unfold(right_link(p, q));
    have p->left == old(root->left->left) by {
        rewrite(old(root->left), p);
        close();
    }
}
```

```expect
pass
```
