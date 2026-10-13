# A copied wide word keeps its live read in each model match arm

```c filename=joined-pointer-detached-child.c
struct node { uint64 tag; struct node *right; struct node *left; };
void copy_tag(struct node *parent, struct node *sibling) { sibling->tag = parent->tag; parent->tag = 1; }
void inspect(struct node *parent, int32 side) {
    struct node *root = parent;
    struct node *sibling;
    while (true) {
        sibling = parent->right;
        if (side) sibling = parent->left;
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
spec enum Parent { Left(struct node*, Pair), Right(struct node*, Pair) }
function parent_identity(m: Parent) -> struct node* {
    match m { Parent::Left(identity, sm) => identity, Parent::Right(identity, sm) => identity, }
}
function direction(m: Parent) -> int32 { match m { Parent::Left(identity, sm) => 1, Parent::Right(identity, sm) => 0, } }
resource parent_at(p: struct node*) {
    field model: Parent;
    match model {
        Parent::Left(identity, sm) => {
            owns identity->tag;
            owns identity->left; owns identity->right;
            owns c: cell(identity->left);
            fact c.model == sm;
        },
        Parent::Right(identity, sm) => {
            owns identity->tag;
            owns identity->left; owns identity->right;
            owns c: cell(identity->right);
            fact c.model == sm;
        },
    }
}
void copy_tag(struct node* parent, struct node* sibling) {
    owns parent->tag;
    owns sibling->tag;
    ensures sibling->tag == old(parent->tag);
    ensures parent->tag == 1;
} by { execute(); simp(); }
void inspect(struct node* parent, int32 side) {
    consumes tree_context: parent_at(parent);
    requires parent == parent_identity(tree_context.model);
    requires side == direction(tree_context.model);
    ensures 1 == 1;
} by {
    execute_until(loop(0));
    loop {
        owns tree_context: parent_at(root);
        invariant parent == parent_identity(tree_context.model);
        invariant side == direction(tree_context.model);
        decreases 0;
        initialize by simp;
        preserve by {
            match tree_context.model {
                Parent::Left(pid, sm) => {
                    have parent == parent_identity(Parent::Left(pid, sm)) by { rewrite(Parent::Left(pid, sm) == tree_context.model); assumption(); }
                    have parent == pid by { unfold(parent_identity(Parent::Left(pid, sm))); simp(); }
                    have side == direction(Parent::Left(pid, sm)) by { rewrite(Parent::Left(pid, sm) == tree_context.model); assumption(); }
                    have side == 1 by { unfold(direction(Parent::Left(pid, sm))); simp(); }
                    let { c: c } = unfold(tree_context);
                    mark tag_inputs;
            match c.model {
                Pair::At(model) => {
                    have Pair::At(model) == sm;
                    unfold(c);
                    step(); step(); step();
                    have sibling == model;
                    have parent->tag == at(tag_inputs, parent->tag);
                    mark rotation;
                    step(copy_tag(parent, sibling), {});
                    have sibling->tag == at(rotation, parent->tag);
                    have model->tag == sibling->tag by { normalize() using { sibling == model; } }
                    have model->tag == at(rotation, parent->tag) by { rewrite(model->tag == sibling->tag); assumption(); }
                    let child = fold(cell(sibling), {model: Pair::At(model)});
                    have child.model == sm by { rewrite(child.model == Pair::At(model)); assumption(); }
                    let tree_context = fold(parent_at(root), {model: Parent::Left(pid, sm)}, {c: child});
                    step(); step();
                },
            }
                },
                Parent::Right(pid, sm) => {
                    have parent == parent_identity(Parent::Right(pid, sm)) by { rewrite(Parent::Right(pid, sm) == tree_context.model); assumption(); }
                    have parent == pid by { unfold(parent_identity(Parent::Right(pid, sm))); simp(); }
                    have side == direction(Parent::Right(pid, sm)) by { rewrite(Parent::Right(pid, sm) == tree_context.model); assumption(); }
                    have side == 0 by { unfold(direction(Parent::Right(pid, sm))); simp(); }
                    let { c: c } = unfold(tree_context);
                    mark tag_inputs;
            match c.model {
                Pair::At(model) => {
                    have Pair::At(model) == sm;
                    unfold(c);
                    step(); step();
                    have sibling == model;
                    have parent->tag == at(tag_inputs, parent->tag);
                    step(); // Finish the selected if continuation.
                    mark rotation;
                    step(copy_tag(parent, sibling), {});
                    have sibling->tag == at(rotation, parent->tag);
                    have model->tag == sibling->tag by { normalize() using { sibling == model; } }
                    have model->tag == at(rotation, parent->tag) by { rewrite(model->tag == sibling->tag); assumption(); }
                    let child = fold(cell(sibling), {model: Pair::At(model)});
                    have child.model == sm by { rewrite(child.model == Pair::At(model)); assumption(); }
                    let tree_context = fold(parent_at(root), {model: Parent::Right(pid, sm)}, {c: child});
                    step(); step();
                },
            }
                },
            }
        }
    }
    execute(); simp();
}
```

```expect
pass
```
