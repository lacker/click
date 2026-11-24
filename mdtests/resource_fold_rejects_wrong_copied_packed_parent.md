# A packed-word fold cannot change the copied parent identity

```c filename=joined-pointer-detached-child.c
struct node { uint64 tag; struct node *right; struct node *left; };
void copy_tag(struct node *parent, struct node *sibling) { sibling->tag = parent->tag; parent->tag = 1; }
void inspect(struct node *parent) {
    struct node *root = parent;
    struct node *sibling;
    while (true) {
        sibling = parent->left;
        copy_tag(parent, sibling);
        parent = sibling;
        break;
    }
}
```

```click
verifying "joined-pointer-detached-child.c";
spec enum Pair { At(struct node*) }
resource cell(p: struct node*) {
    field model: Pair;
    match model { Pair::At(identity) => {
        owns p->tag;
        fact p == identity;
    }, }
}
spec enum Tagged { At(struct node*, struct node*) }
resource tagged_at(p: struct node*) {
    field model: Tagged;
    match model { Tagged::At(identity, above) => {
        owns identity->tag;
        fact p == identity;
        fact identity->tag == address(above) + (identity->tag & 1);
        fact (identity->tag & 1) == 1;
    }, }
}
spec enum Parent { At(struct node*, Pair) }
function parent_identity(m: Parent) -> struct node* {
    match m { Parent::At(identity, sm) => identity, }
}
resource parent_at(p: struct node*) {
    field model: Parent;
    match model {
        Parent::At(identity, sm) => {
            owns identity->tag;
            fact identity->tag == address(identity) + (identity->tag & 1);
            fact (identity->tag & 1) == 1;
            owns identity->left;
            owns c: cell(identity->left);
            fact c.model == sm;
        },
    }
}
void copy_tag(struct node* parent, struct node* sibling) {
    owns parent->tag;
    owns sibling->tag;
    ensures sibling->tag == old(parent->tag);
    ensures parent->tag == 1;
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
                Parent::At(pid, sm) => {
                    have parent == parent_identity(Parent::At(pid, sm)) by { rewrite(Parent::At(pid, sm), tree_context.model); close(); }
                    have parent == pid by { unfold(parent_identity(Parent::At(pid, sm))); close(); }
                    let { c: c } = unfold(tree_context);
                    have parent->tag == address(pid) + (parent->tag & 1);
                    have (parent->tag & 1) == 1;
                    mark tag_inputs;
            match c.model {
                Pair::At(model) => {
                    unfold(c);
                    step();
                    have sibling == model;
                    have parent->tag == at(tag_inputs, parent->tag);
                    have parent->tag == address(pid) + (parent->tag & 1) by { rewrite(parent->tag, at(tag_inputs, parent->tag)); close(); }
                    have (parent->tag & 1) == 1 by { rewrite(parent->tag, at(tag_inputs, parent->tag)); close(); }
                    mark rotation;
                    step(copy_tag);
                    have sibling->tag == at(rotation, parent->tag);
                    have model->tag == sibling->tag by { normalize() using { sibling == model; }; }
                    have model->tag == at(rotation, parent->tag) by { rewrite(model->tag, sibling->tag); close(); }
                    have model->tag == address(pid) + (model->tag & 1) by { rewrite(model->tag, at(rotation, parent->tag)); close(); }
                    have (model->tag & 1) == 1 by { rewrite(model->tag, at(rotation, parent->tag)); close(); }
                    let packed = fold(tagged_at(model), {model: Tagged::At(model, 0)}) {
                        requires model->tag == address(0) + (model->tag & 1) by close();
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
fail: `have` failed for `model->tag == (address(0) + (model->tag & 1))`
```
