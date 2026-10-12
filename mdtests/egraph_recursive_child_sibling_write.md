# Recursive child matching across a sibling-field write

Unfold, write the integer sibling field, and refold the same recursive children
at the original full parent carrier `p`. Preserve the identical model, including
its numerical `id`; address equality does not transfer native designation.

```c filename=egraph_reduce.c
struct node { struct node *left; struct node *right; int tag; };
void roundtrip(struct node *p) { p->tag = 1; }
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
   owns p->tag;
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
   step();
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
