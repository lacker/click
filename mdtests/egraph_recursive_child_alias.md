# Recursive child refolding preserves the parent carrier and model identity

Unfold and refold the same full parent pointer value without C writes. The
model retains its original `id`, which is numerically equal to `p`; that fact
does not transfer `p`'s native record designation to `id`. Child indices retain
the checked pointer-read definitions used to construct them.

```c filename=egraph_reduce.c
struct node { struct node *left; struct node *right; };
void roundtrip(struct node *p) {}
```

```click
verifying "egraph_reduce.c";
spec enum Tree { Empty, Node(struct node*, Tree, Tree) }
resource tree(p: struct node*) {
 field model: Tree;
 match model {
  Tree::Empty => { fact p == 0; },
  Tree::Node(id, lm, rm) => {
   owns p->left;
   owns p->right;
   owns left: tree(p->left);
   owns right: tree(p->right);
   fact p != 0;
   fact p == id;
   fact left.model == lm;
   fact right.model == rm;
  },
 }
}
void roundtrip(struct node* p) {
 owns t: tree(p);
 requires t.model != Tree::Empty;
 ensures t.model == old(t.model);
} by {
 match t.model {
  Tree::Empty => { contradiction(t.model == Tree::Empty); },
  Tree::Node(id, lm, rm) => {
   let { left: l, right: r } = unfold(t);
   let t = fold(tree(p), { model: Tree::Node(id, lm, rm) }, { left: l, right: r });
   execute();
   simp();
  },
 }
}
```

```expect
pass
```
