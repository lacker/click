# A named root-link call preserves wide field-read congruence

The helper changes only the root link. Nested modeled children retain their
pointer identities when the root changes. After the call, `near == rid`
implies equal reads of their eight-byte tag in the same current memory.
The 32-bit counterpart already worked through the int32 equality graph;
the wide route must preserve all eight bytes and the recorded read states.
The subsequent store also preserves current-read congruence and supplies its
exact wide value through the recorded pointer alias.

```c filename=probe.c
struct node { unsigned long tag; struct node *left; struct node *right; };
struct root { struct node *node; };
void helper(struct node *p, struct node *q, struct root *root) { root->node = q; }
void probe(struct node *p, struct root *root) {
    struct node *cursor = p->right;
    struct node *near = cursor->left;
    p->right = near;
    cursor->left = p;
    helper(p, cursor, root);
    cursor = near;
    near = cursor->right;
    near->tag = 0;
}
```

```click
verifying "probe.c";
spec enum Leaf { At(struct node*) }
spec enum Branch { At(struct node*, Leaf) }
spec enum Outer { At(struct node*, Branch) }
resource leaf(p: struct node*) {
 field model: Leaf;
 match model { Leaf::At(id) => { owns p->tag; fact p == id; } }
}
resource branch(p: struct node*) {
 field model: Branch;
 match model { Branch::At(id, lm) => {
  owns p->right; owns child: leaf(p->right);
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
  let {child: far_tree} = unfold(near_tree);
  unfold(far_tree);
  have p->right == sid;
  have sid->left == nid;
  have nid->right == rid;
  step(); step(); step(); step(); step(); step();
  let { after: c } = step(helper, { before: c });
  step();
  have cursor == nid;
  have cursor->right == rid;
  step();
  have near == rid;
  have near->tag == rid->tag by { normalize() using { near == rid; }; }
  step();
  have near->tag == rid->tag by { normalize() using { near == rid; }; }
  have rid->tag == 0u64 by { normalize() using { near == rid; }; }
  step();
 } }
 } }
 } }
}
```

```expect
pass
```
