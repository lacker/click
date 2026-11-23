# Preserve a child pointer across a named-root call and rotation stores

Keep the nested child resources folded through `helper` and unfold them when
the caller reads their fields. The final stores use footprint separation and
`preserve` to keep the other pointer fields at their saved values.

```c filename=probe.c
struct node { unsigned long tag; struct node *right; struct node *left; };
struct root { struct node *node; };
void helper(struct node *p, struct node *q, struct root *root) { root->node = q; }
void probe(struct node *p, struct root *root) {
    struct node *cursor = p->right;
    struct node *near = cursor->left;
    p->right = near;
    cursor->left = p;
    helper(p, cursor, root);
    cursor = near;
    near = cursor->left;
    cursor->left = 0;
    near->right = cursor;
}
```

```click
verifying "probe.c";
spec enum Leaf { At(struct node*) }
spec enum Branch { At(struct node*, Leaf) }
spec enum Outer { At(struct node*, Branch) }
resource leaf(p: struct node*) {
 field model: Leaf;
 match model { Leaf::At(id) => { owns p->tag; owns p->left; owns p->right; fact p->left == 0; fact p->right == 0; fact p == id; } }
}
resource branch(p: struct node*) {
 field model: Branch;
 match model { Branch::At(id, lm) => {
  owns p->left; owns p->right; fact p->right == 0; owns child: leaf(p->left);
  fact p == id; fact child.model == lm;
 } }
}
resource shell(p: struct node*) {
 field model: Outer;
 match model { Outer::At(id, bm) => {
  owns p->tag; owns p->left; owns child: branch(p->left);
  fact p == id; fact child.model == bm;
 } }
}
spec enum Context { Top }
resource context(p: struct node*, root: struct root*) { field model: Context; match model { Context::Top => { owns root->node; fact root->node == p; } } }
void helper(struct node *p, struct node *q, struct root *root) {
 consumes before: context(p, root);
 produces after: context(q, root);
} by { match before.model { Context::Top => { unfold(before); step_until(function.exit); let after = fold(context(q, root), {model: Context::Top}); solve(); } } }
void probe(struct node *p, struct root *root) {
 owns p->tag; owns p->right;
 consumes b: shell(p->right); consumes c: context(p, root);
 ensures 1 == 1;
} by {
 match b.model { Outer::At(sid, bm) => {
 match bm { Branch::At(nid, lm) => {
 match lm { Leaf::At(rid) => {
  let {child: near_tree} = unfold(b);
  have p->right == sid by { known(); }
  step(); step(); step(); step(); step(); step();
  let { after: c } = step(helper, { before: c });
  step();
  let {child: far_tree} = unfold(near_tree);
  have cursor == nid by { known(); }
  step();
  unfold(far_tree);
  have near == rid by { known(); }
  have rid->left == 0 by { known(); }
  have separate(memory(rid->left), memory(nid->left)) by { known(); }
  have separate(memory(nid->right), memory(rid->right)) by { known(); }
  have cursor->left == near by { known(); }
  have cursor->left == rid by { rewrite(cursor->left, near); known(); }
  have nid->right == 0 by { known(); }
  have separate(memory(cursor->left), memory(rid->left)) by {
   rewrite(cursor, nid); known();
  }
  have separate(memory(cursor->left), memory(nid->right)) by { known(); }
  mark before_detach;
  step();
  have separate(statement(7).footprint, memory(rid->left)) by {
   normalize() using { separate(memory(cursor->left), memory(rid->left)); };
  }
  have rid->left == at(before_detach, rid->left) by {
   preserve(memory(rid->left), statement(7));
  }
  have rid->left == 0 by { rewrite(rid->left, at(before_detach, rid->left)); known(); }
  have separate(statement(7).footprint, memory(nid->right)) by {
   normalize() using { separate(memory(cursor->left), memory(nid->right)); };
  }
  have nid->right == at(before_detach, nid->right) by {
   preserve(memory(nid->right), statement(7));
  }
  have nid->right == 0 by { rewrite(nid->right, at(before_detach, nid->right)); known(); }
  have separate(memory(rid->left), memory(near->right)) by {
   rewrite(near, rid); normalize();
  }
  have separate(memory(nid->right), memory(near->right)) by {
   rewrite(near, rid); known();
  }
  mark before_attach;
  step();
  have near->right == cursor by { known(); }
  have rid->right == cursor by { rewrite(rid, near); known(); }
  have separate(statement(8).footprint, memory(rid->left)) by {
   normalize() using { separate(memory(rid->left), memory(near->right)); };
  }
  have rid->left == at(before_attach, rid->left) by {
   preserve(memory(rid->left), statement(8));
  }
  have rid->left == 0 by { rewrite(rid->left, at(before_attach, rid->left)); known(); }
  have separate(statement(8).footprint, memory(nid->right)) by {
   normalize() using { separate(memory(nid->right), memory(near->right)); };
  }
  have nid->right == at(before_attach, nid->right) by {
   preserve(memory(nid->right), statement(8));
  }
  have nid->right == 0 by { rewrite(nid->right, at(before_attach, nid->right)); known(); }
  step_until(function.exit); solve();
 } }
 } }
 } }
}
```

```expect
pass
```
