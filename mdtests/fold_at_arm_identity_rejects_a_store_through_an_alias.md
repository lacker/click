# A refold at the arm identity sees a store through an aliasing pointer

The store goes through `q`, and the contract states `q == p`, so it writes
the node's own `right` field under another spelling. Reading `id->right`
through the graph-aligned run slot returns the stored null pointer, never the
value the unfold seeded, and the refold with the old right child is refused.

```c filename=fold_at_arm_identity_rejects_a_store_through_an_alias.c
struct node { struct node *left; struct node *right; int tag; };
void roundtrip(struct node *p, struct node *q) { q->right = 0; }
```

```click
verifying "fold_at_arm_identity_rejects_a_store_through_an_alias.c";

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

void roundtrip(struct node* p, struct node* q) {
    owns t: tree(p);
    requires q == p;
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            have separate(memory(q->right), memory(p->left)) by {
                close();
            }
            mark before;
            step();
            have separate(statement(0).footprint, memory(p->left)) by {
                close();
            }
            have p->left == at(before, p->left) by {
                preserve(memory(p->left), statement(0));
            }
            let t = fold(tree(id), { model: Tree::Node(id, lm, rm), left: l, right: r });
        },
    }
}
```

```expect
fail: child `right` is not proven to have the arguments the parent body gives it
```
