# A changed pointer field is not its old value through an alias

```c filename=nested-loop.c
struct node { struct node *tag; struct node *right; struct node *left; };
void copy_tag(struct node *p, struct node *q) { q->tag = p->tag; p->tag = 0; q->right = 0; }
void inspect(struct node *p) { struct node *root = p; struct node *q; while (true) { q = p->right; copy_tag(p, q); p = q; break; } }
```

```click
verifying "nested-loop.c";
spec enum Pair { At(struct node*) }
resource cell(p: struct node*) {
 field model: Pair;
 match model { Pair::At(identity) => {
  owns p->tag; owns p->right;
  fact p == identity;
 }, }
}
void copy_tag(struct node *p, struct node *q) {
 owns p->tag; owns q->tag; owns q->right;
 ensures q->tag == old(p->tag); ensures p->tag == 0; ensures q->right == 0;
}
spec enum Tree { At(struct node*, Pair) }
function tree_identity(t: Tree) -> struct node* { match t { Tree::At(id, c) => id, } }
resource parent(p: struct node*) {
 field model: Tree;
 match model { Tree::At(id, cm) => {
 owns id->right; owns id->tag;
 owns child: cell(id->right);
 fact child.model == cm;
 }, }
}
void inspect(struct node *p) {
 consumes t: parent(p);
 requires p == tree_identity(t.model);
 ensures 1 == 1;
} by {
 step_until(loop(0).entry);
 loop { owns t: parent(root); invariant p == tree_identity(t.model); decreases 0; initialize by close(); maintain by {
 match t.model { Tree::At(pid, cm) => {
 have p == tree_identity(Tree::At(pid, cm)) by { rewrite(Tree::At(pid, cm), t.model); close(); }
 have p == pid by { unfold(tree_identity(Tree::At(pid, cm))); close(); }
 let { child: c } = unfold(t);
 match c.model {
  Pair::At(identity) => {
   have Pair::At(identity) == cm;
   unfold(c);
   step();
   have q == identity;
   mark rotation;
   step(copy_tag);
   have q->tag == at(rotation,p->tag);
   have identity->tag == q->tag by { normalize() using { q == identity; }; }
   have identity->tag == at(rotation,p->tag) by { rewrite(identity->tag, q->tag); close(); }
   have identity->right == at(rotation, q->right) by { normalize() using { q == identity; }; }
   let child = fold(cell(q), { model: Pair::At(identity) });
   have child.model == cm by { rewrite(child.model, Pair::At(identity)); close(); }
   let t = fold(parent(root), { model: Tree::At(pid, cm), child: child });
   step(); step();
  },
 }
 }, }
 } }
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
