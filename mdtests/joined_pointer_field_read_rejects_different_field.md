# A joined pointer read does not identify a different field

```c filename=joined-pointer-field-read.c
struct node { uint64 tag; struct node *right; struct node *left; };
void inspect(struct node *parent) {
    struct node *root = parent;
    struct node *sibling;
    struct node *child;
    while (true) {
        sibling = parent->left;
        child = sibling->left;
        parent = child;
        break;
    }
}
```

```click
verifying "joined-pointer-field-read.c";
spec enum Identity { At(struct node*) }
spec enum Pair { At(struct node*, Identity) }
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
    match model { Identity::At(identity) => { owns p->right; fact p == identity; }, }
}
resource cell(p: struct node*) {
    field model: Pair;
    match model {
        Pair::At(identity, child) => {
            owns p->left;
            owns l: leaf_at(p->left);
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
void inspect(struct node* parent) {
    owns tree_context: parent_at(parent);
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
                Pair::At(model, lm) => {
                    let { l: l } = unfold(c);
                    have parent->left == model by { close(); }
                    have defined(parent->right) by { rewrite(parent, pid); normalize(); }
                    mark before_sibling;
                    have defined(at(before_sibling, pid->right)) by { normalize(); }
                    step();
                    have separate(loop(0).statement(0).footprint, memory(parent->right)) by { close(); }
                    have defined(parent->right) by {
                        preserve(memory(parent->right), loop(0).statement(0));
                    }
                    have parent->right == at(before_sibling, parent->right) by {
                        preserve(memory(parent->right), loop(0).statement(0));
                    }
                    have separate(loop(0).statement(0).footprint, memory(parent->left)) by { close(); }
                    have parent->left == at(before_sibling, parent->left) by {
                        preserve(memory(parent->left), loop(0).statement(0));
                    }
                    have separate(loop(0).statement(0).footprint, memory(parent->left->left)) by { close(); }
                    have parent->left->left == at(before_sibling, parent->left->left) by {
                        preserve(memory(parent->left->left), loop(0).statement(0));
                    }
                    have sibling == model by { close(); }
                    mark split;
                    match f.model ensuring {
                        owns f: focus_at(parent->right);
                        fact f.model == at(split, f.model);
                    } {
                        Focus::Empty => {
                            have at(split, f.model) == Focus::Empty;
                            have f.model == at(split, f.model);
                        },
                        Focus::Live(identity) => {
                            have at(split, f.model) == Focus::Live(identity);
                            have f.model == at(split, f.model);
                        },
                    }
                    have sibling->left == at(before_sibling, parent->left->left) by { close(); }
                    mark before_child;
                    step();
                    have child == at(before_child, sibling->left) by { close(); }
                    match lm {
                        Identity::At(leaf) => {
                            unfold(l);
                            have sibling == model;
                            have at(before_sibling, parent->left->left) == leaf by { close(); }
                            have at(before_child, sibling->left) == at(before_sibling, parent->left->left) by { close(); }
                            have child == leaf by { close(); }
                            have sibling->left == child;
                            have model->right == leaf by {
                                normalize() using { sibling == model; sibling->left == child; child == leaf; };
                            }
                            let l = fold(leaf_at(parent->left->left), { model: Identity::At(leaf) });
                            let c = fold(cell(parent->left), { model: Pair::At(model, Identity::At(leaf)), l: l });
                            have f.model == fm;
                            let tree_context = fold(parent_at(root), { model: Parent::At(pid, Pair::At(model, Identity::At(leaf)), fm), c: c, f: f });
                            step(); step();
                        },
                    }
                },
            }
                },
            }
        }
    }
}
```

```expect
fail: `normalize using` goal did not normalize to true
```
