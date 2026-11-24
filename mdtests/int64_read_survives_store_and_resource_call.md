# A framed tag survives a store followed by a resource-transfer call

```c filename=store_before_resource_call.c
struct Node { long tag; struct Node *next; };
struct Root { struct Node *node; };
void helper(struct Node *p, struct Node *q, struct Root *root) { root->node = q; }
void caller(struct Node *p, struct Node *q, struct Root *root) {
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
void caller(struct Node* p, struct Node* q, struct Root* root) {
    consumes before: link(p, root);
    owns p->tag;
    owns p->next;
    owns q->tag;
    requires (q->tag & 1) == 1;
    produces after: link(q, root);
    ensures (q->tag & 1) == 1;
} by {
    step();
    have (q->tag & 1) == 1;
    mark call_entry;
    let {after: after} = step(helper, {before: before});
    have q->tag == at(call_entry, q->tag) by close();
    have (q->tag & 1) == 1;
}
```

```expect
pass
```
