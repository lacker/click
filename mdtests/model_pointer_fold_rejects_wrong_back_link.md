# A modeled back-link fold rejects a different target

The source model proves a back-link to `pid`; the proposed model instead
requires `rid`. Retaining typed-read definitions must not identify these
unrelated model values.

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
 fact p == pid; fact pid->left == qid; fact qid->left == pid;
 }, }
}
resource links(p: struct node*, child: struct node*) {
 owns p->left; owns p->right; fact p->left == child;
}
resource fields(p: struct node*) {
 field model: Triple;
 match model { Triple::At(pid,qid,rid) => {
 owns qid->left; owns qid->right;
 fact p == qid; fact qid->left == pid;
 }, }
}
void recombine(struct node *p) {
 consumes tree: pair(p);
 ensures 1 == 1;
} by {
 match tree.model { Triple::At(pid,qid,rid) => {
 unfold(tree);
 have p->left == qid by { close(); }
 fold(links(qid,pid));
 unfold(links(qid,pid));
 have qid->left == pid by { close(); }
 let check = fold(fields(qid), { model: Triple::At(rid,qid,rid) });
 step_until(function.exit); normalize();
 }, }
}
```

```expect
fail: unproved obligation: `qid->left == rid`
```
