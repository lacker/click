# A rotation callback may not relink the tree it was handed

This is the negative half of `mdtests/augment_rotate_model_callback.md`. With
the links inside the model, `AugmentRotate(t: tree_at(new))` hands the callback
the rebuilt tree as a proof parameter and takes it back with
`t.model == old(t.model)`: the two link cells of every node are owned by `t`,
so a callback has no way to reach them except through the model, and no way to
return the model unchanged after rewriting one.

`clobber` writes `old->left`, a link the rotation left inside that tree, so its
own contract has to own `old->left` on top of `t` and the two augmentation
cells, and it cannot promise the model back. `AugmentRotate(&clobber)` never
forms.

The refusal is decided by the wider interface before the missing guarantee is
reached: adding `ensures t.model == old(t.model)` to `clobber`'s contract, a
claim its body does not honour for a tree that contains `old`, does not change
the verdict, because ownership of `old->left` is already outside what the named
contract lends. The guarantee itself is load-bearing on the positive side,
where `rotate_left` can only state the rotated model because the callback
returns `t.model` unchanged; `steal`, whose contract consumes tree ownership
the named contract only lends, is refused the same way as in
`mdtests/augment_rotate_callback_rejects_consumed_shape.md`.

```c filename=augment_rotate_model_relink.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

struct node *rotate_left(struct node *node,
                         void (*augment_rotate)(struct node *old, struct node *new)) {
    struct node *pivot = node->right;
    struct node *middle = pivot->left;
    node->right = middle;
    pivot->left = node;
    augment_rotate(node, pivot);
    return pivot;
}

void bump(struct node *old, struct node *new) { new->augmented = old->augmented + 1; }
void reset(struct node *old, struct node *new) { old->augmented = 0; new->augmented = 0; }
void clobber(struct node *old, struct node *new) { new->augmented = 0; old->left = 0; }
void steal(struct node *old, struct node *new) { new->augmented = old->augmented; }

struct node *rotate_clobber(struct node *node) {
    return rotate_left(node, &clobber);
}
```

```click
verifying "augment_rotate_model_relink.c";

spec enum Shape {
    Empty,
    Node(struct node*, Shape, Shape),
}

resource tree_at(p: struct node*) {
    field model: Shape;
    match model {
        Shape::Empty => { fact p == 0; },
        Shape::Node(identity, left_model, right_model) => {
            owns p->left;
            owns p->right;
            owns left: tree_at(p->left);
            owns right: tree_at(p->right);
            fact p != 0;
            fact p == identity;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

function shape_left(tree: Shape) -> Shape {
    match tree {
        Shape::Empty => Shape::Empty,
        Shape::Node(identity, left, right) => left,
    }
}

function shape_right(tree: Shape) -> Shape {
    match tree {
        Shape::Empty => Shape::Empty,
        Shape::Node(identity, left, right) => right,
    }
}

contract AugmentRotate(t: tree_at(new)) for void(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= old->augmented;
    requires old->augmented < 1000;
    owns t;
    owns old->augmented;
    owns new->augmented;
    ensures t.model == old(t.model);
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
}

void clobber(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    owns t: tree_at(new);
    owns old->left;
    owns old->augmented;
    owns new->augmented;
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
} by {
    execute();
    simp();
}

struct node* rotate_left(
    struct node* node,
    void (*augment_rotate)(struct node*, struct node*)
) {
    requires AugmentRotate(augment_rotate);
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes node->left;
    consumes node->right;
    consumes l: tree_at(node->left);
    consumes r: tree_at(node->right);
    requires r.model != Shape::Empty;
    owns node->augmented;
    owns node->right->augmented;
    produces rotated: tree_at(result);

    ensures result == old(node->right);
    ensures rotated.model == Shape::Node(old(node->right),
        Shape::Node(node, old(l.model), shape_left(old(r.model))),
        shape_right(old(r.model)));
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    match r.model {
        Shape::Empty => { contradiction(r.model == Shape::Empty); },
        Shape::Node(pivot_node, middle_model, far_model) => {
            unfold(r) as { left: m, right: z };
            step();
            step();
            step();
            step();
            step();
            step();
            let lower = fold(tree_at(node), {
                model: Shape::Node(node, l.model, m.model)
            }, { left: l, right: m });
            let rotated = fold(tree_at(pivot), {
                model: Shape::Node(pivot, lower.model, z.model)
            }, { left: lower, right: z });
            have shape_left(old(r.model)) == middle_model by {
                rewrite(old(r.model) == Shape::Node(pivot_node, middle_model, far_model));
                unfold(shape_left(Shape::Node(pivot_node, middle_model, far_model)));
                normalize();
            }
            have shape_right(old(r.model)) == far_model by {
                rewrite(old(r.model) == Shape::Node(pivot_node, middle_model, far_model));
                unfold(shape_right(Shape::Node(pivot_node, middle_model, far_model)));
                normalize();
            }
            step(AugmentRotate(rotated));
            have rotated.model == Shape::Node(old(node->right),
                Shape::Node(node, old(l.model), shape_left(old(r.model))),
                shape_right(old(r.model))) by {
                rewrite(shape_left(old(r.model)) == middle_model);
                rewrite(shape_right(old(r.model)) == far_model);
                simp();
            }
            step();
            simp();
        },
    }
}

struct node* rotate_clobber(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes node->left;
    consumes node->right;
    consumes a: tree_at(node->left);
    consumes b: tree_at(node->right);
    requires b.model != Shape::Empty;
    owns node->augmented;
    owns node->right->augmented;
    produces rotated: tree_at(result);

    ensures result == old(node->right);
    ensures rotated.model == Shape::Node(old(node->right),
        Shape::Node(node, old(a.model), shape_left(old(b.model))),
        shape_right(old(b.model)));
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    let rotated = step(rotate_left(node, &clobber), { l: a, r: b });
    execute();
    simp();
}

struct node* rotate_reset(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes node->left;
    consumes node->right;
    consumes a: tree_at(node->left);
    consumes b: tree_at(node->right);
    requires b.model != Shape::Empty;
    owns node->augmented;
    owns node->right->augmented;
    produces rotated: tree_at(result);

    ensures result == old(node->right);
    ensures rotated.model == Shape::Node(old(node->right),
        Shape::Node(node, old(a.model), shape_left(old(b.model))),
        shape_right(old(b.model)));
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    let rotated = step(rotate_left(node, &reset), { l: a, r: b });
    execute();
    simp();
}
```

```expect
fail: function `clobber` does not satisfy named contract `AugmentRotate`
```
