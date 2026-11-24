# A modeled fold still requires the actual pointer field value

A model binding may use another proved spelling of the same pointer. The fold must compare the recorded typed reads without inventing a link value.

```c filename=recombine.c
struct node { struct node *tag; struct node *right; struct node *left; };
void recombine(struct node *p) { }
```

```click
verifying "recombine.c";
spec enum Triple { At(struct node*, struct node*, struct node*), }
resource pair(p: struct node*) {
 field model: Triple;
 match model { Triple::At(pid,qid,rid) => {
 owns pid->left; owns qid->right; owns qid->left;
 fact p == pid; fact pid->left == qid; fact qid->left == rid;
 }, }
}
resource links(p: struct node*, child: struct node*) {
 owns p->left; owns p->right; fact p->left == child;
}
resource fields(p: struct node*) {
 field model: Triple;
 match model { Triple::At(pid,qid,rid) => {
 owns qid->left; owns qid->right;
 fact p == qid; fact qid->left == rid;
 }, }
}
void recombine(struct node *p) {
 consumes tree: pair(p);
 ensures 1 == 1;
} by {
 match tree.model { Triple::At(pid,qid,rid) => {
 unfold(tree);
 have p->left == qid;
 fold(links(qid,rid));
 unfold(links(qid,rid));
 have qid->left == rid by close();
 let check = fold(fields(qid), { model: Triple::At(pid,qid,pid) });
 step_until(function.exit); normalize();
 }, }
}
```

```expect
fail: unproved obligation: `qid->left == pid`
```
