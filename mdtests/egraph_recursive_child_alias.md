# Recursive child matching through an equal parent address

Unfold and refold without C writes. Fold must retain the checked pointer-read
definitions used to construct child indices, so the graph can match them
through equal parent addresses.

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
   let t = fold(tree(id), { model: Tree::Node(id, lm, rm), left: l, right: r });
   step_until(function.exit);
   close();
  },
 }
}
```

```expect
pass
```
