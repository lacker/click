# A stored pointer keeps its block identity across a framed call

```c filename=store_before_resource_call.c
struct Node { unsigned long tag; struct Node *next; };
struct Root { struct Node *node; };
void helper(struct Node *p, struct Node *q, struct Root *root) { root->node = q; }
struct Node *choose(struct Node *q) { return q; }
void caller(struct Node *p, struct Node *q, struct Node *t, struct Root *root) {
    struct Node *r = choose(q);
    struct Node *s = choose(t);
    r->next = s->next;
    p->next = q;
    helper(p, q, root);
}
```
```click
verifying "store_before_resource_call.c";
spec enum Tag { Here, }
resource link(p: struct Node*, root: struct Root*) {
    field model: Tag;
    owns root->node;
    fact model == Tag::Here;
    fact root->node == p;
}
void helper(struct Node* p, struct Node* q, struct Root* root) {
    consumes before: link(p, root);
    owns p->tag;
    produces after: link(q, root);
    ensures p->tag == old(p->tag);
} by {
    unfold(before); step_until(function.exit);
    let after = fold(link(q, root), { model: Tag::Here }); close();
}
struct Node* choose(struct Node* q) {
    consumes q->next;
    requires q->next == 0;
    produces result->next;
    ensures result->next == 0;
}
void caller(struct Node* p, struct Node* q, struct Node* t, struct Root* root) {
    consumes before: link(p, root);
    owns p->tag;
    owns p->next;
    consumes q->next;
    consumes t->next;
    requires q->next == 0;
    requires t->next == 0;
    produces after: link(q, root);
} by {
    step_until(call(helper, 0).entry);
    have r->next == 0;
    mark call_entry;
    let {after: after} = step(helper, {before: before});
    have r->next == at(call_entry, r->next) by close();
    have r->next == 0;
}
```

```expect
pass
```
