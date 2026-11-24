# A branch interface rejects a changed aliased wide word

```c filename=joined-pointer-detached-child.c
struct node { uint64 tag; struct node *right; struct node *left; };
void set_tag(struct node *p) { p->tag = 1; }
void inspect(struct node *parent) {
    struct node *root = parent;
    struct node *sibling;
    struct node *child;
    struct node *far;
    while (true) {
        sibling = parent->left;
        far = sibling->left;
        child = sibling->right;
        parent->left = child;
        sibling->right = parent;
        far->tag = (uint64)sibling | 1;
        if (child) { set_tag(child); far->tag = 0; }
        parent = child;
        break;
    }
}
```

```click
verifying "joined-pointer-detached-child.c";
spec enum Identity { Empty, At(struct node*) }
spec enum Pair { At(struct node*, struct node*, Identity) }
spec enum Focus { Empty, Live(struct node*) }
resource focus_at(p: struct node*) {
    field model: Focus;
    match model {
        Focus::Empty => { fact p == 0; },
        Focus::Live(identity) => { owns p->right; fact p == identity; fact p != 0; },
    }
}
resource leaf_at(p: struct node*) {
    field model: Identity;
    match model { Identity::Empty => { fact p == 0; }, Identity::At(identity) => { owns p->tag; fact p == identity; fact p != 0; }, }
}
resource cell(p: struct node*) {
    field model: Pair;
    match model {
        Pair::At(identity, far_identity, child) => {
            owns p->left;
            owns p->left->tag;
            fact p->left == far_identity;
            owns p->right;
            owns l: leaf_at(p->right);
            fact p == identity;
            fact l.model == child;
        },
    }
}
spec enum Parent { At(struct node*, Pair, Focus) }
function parent_identity(m: Parent) -> struct node* {
    match m { Parent::At(identity, sm, fm) => identity, }
}
resource parent_at(p: struct node*) {
    field model: Parent;
    match model {
        Parent::At(identity, sm, fm) => {
            owns identity->left;
            owns identity->right;
            owns c: cell(identity->left);
            owns f: focus_at(identity->right);
            fact c.model == sm;
            fact f.model == fm;
        },
    }
}
void set_tag(struct node* p) {
    owns p->tag;
    ensures p->tag == 1;
}
void inspect(struct node* parent) {
    consumes tree_context: parent_at(parent);
    requires parent == parent_identity(tree_context.model);
    ensures 1 == 1;
} by {
    step_until(loop(0).entry);
    loop {
        owns tree_context: parent_at(root);
        invariant parent == parent_identity(tree_context.model);
        decreases 0;
        initialize by close();
        maintain by {
            match tree_context.model {
                Parent::At(pid, sm, fm) => {
                    have parent == parent_identity(Parent::At(pid, sm, fm)) by { rewrite(Parent::At(pid, sm, fm), tree_context.model); close(); }
                    have parent == pid by { unfold(parent_identity(Parent::At(pid, sm, fm))); close(); }
                    let { c: c, f: f } = unfold(tree_context);
            match c.model {
                Pair::At(model, far_identity, lm) => {
                    let { l: l } = unfold(c);
                    step();
                    mark split;
                    match f.model ensuring {
                        owns nf: focus_at(pid->right);
                        fact nf.model == at(split, f.model);
                    } {
                        Focus::Empty => {
                            have at(split, f.model) == Focus::Empty;
                            unfold(f);
                            let nf = fold(focus_at(pid->right), { model: Focus::Empty });
                            have nf.model == at(split, f.model);
                        },
                        Focus::Live(identity) => {
                            have at(split, f.model) == Focus::Live(identity);
                            unfold(f);
                            let nf = fold(focus_at(pid->right), { model: Focus::Live(identity) });
                            have nf.model == at(split, f.model);
                        },
                    }
                    step(); step(); step(); step(); step();
                    have sibling == model;
                    have far == far_identity;
                    have far->tag == (address(sibling) | 1);
                    have far_identity->tag == (address(model) | 1) by { close() using { far->tag == (address(sibling) | 1); far == far_identity; sibling == model; }; }
                    mark before_update;
                    match lm ensuring {
                        owns after: leaf_at(child);
                        fact after.model == lm;
                        fact far_identity->tag == (address(model) | 1);
                    } {
                        Identity::Empty => {
                            have l.model == Identity::Empty;
                            unfold(l);
                            have child == 0;
                            step(); step();
                            let after = fold(leaf_at(child), {model: Identity::Empty});
                            have after.model == lm;
                            have far_identity->tag == (address(model) | 1) by { normalize() using { at(before_update, far_identity->tag == (address(model) | 1)); far == far_identity; sibling == model; }; }
                        },
                        Identity::At(leaf) => {
                            have l.model == Identity::At(leaf);
                            unfold(l);
                            have child == leaf;
                            have child != 0;
                            step();
                            step(set_tag);
                            step();
                            let after = fold(leaf_at(child), {model: Identity::At(leaf)});
                            have after.model == lm;
                        },
                    }
                    step(); step();
                },
            }
                },
            }
        }
    }
}
```

```expect
fail: `branch ensuring` did not establish fact
```
