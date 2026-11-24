# A rotation callback may not relink the tree it was handed

This is the negative half of a rotation callback contract over a modeled
tree. With the links inside the model, `AugmentRotate(t: tree_at(new))` hands the callback
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

contract void AugmentRotate(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= old->augmented;
    requires old->augmented < 1000;
    owns t: tree_at(new);
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
            let { left: m, right: z } = unfold(r);
            // Carry the untouched link reads across each store before folding.
            step_until(statement(2).entry);
            have defined(node->left) by { normalize(); }
            have separate(memory(node->left), memory(node->right)) by { close(); }
            have defined(pivot->right) by { normalize(); }
            have separate(memory(pivot->right), memory(node->right)) by { close(); }
            have node->left == old(node->left) by close();
            have pivot->right == old(node->right->right) by close();
            mark before_right;
            step_until(statement(3).entry);
            have separate(statement(2).footprint, memory(node->left)) by {
                normalize() using { at(before_right, separate(memory(node->left), memory(node->right))); };
            }
            have defined(node->left) by { preserve(memory(node->left), statement(2)); }
            have node->left == at(before_right, node->left) by { preserve(memory(node->left), statement(2)); }
            have separate(statement(2).footprint, memory(pivot->right)) by {
                normalize() using { at(before_right, separate(memory(pivot->right), memory(node->right))); };
            }
            have defined(pivot->right) by { preserve(memory(pivot->right), statement(2)); }
            have pivot->right == at(before_right, pivot->right) by { preserve(memory(pivot->right), statement(2)); }

            have separate(memory(node->left), memory(pivot->left)) by { close(); }
            have defined(node->right) by { normalize(); }
            have node->right == middle by { normalize(); }
            have middle == old(node->right->left) by { close(); }
            have separate(memory(node->right), memory(pivot->left)) by { close(); }
            have defined(pivot->right) by { normalize(); }
            have separate(memory(pivot->right), memory(pivot->left)) by { close(); }
            mark before_left;
            step_until(statement(4).entry);
            have separate(statement(3).footprint, memory(node->left)) by {
                normalize() using { at(before_left, separate(memory(node->left), memory(pivot->left))); };
            }
            have defined(node->left) by { preserve(memory(node->left), statement(3)); }
            have separate(statement(3).footprint, memory(node->right)) by {
                normalize() using { at(before_left, separate(memory(node->right), memory(pivot->left))); };
            }
            have defined(node->right) by { preserve(memory(node->right), statement(3)); }
            have node->right == at(before_left, node->right) by { preserve(memory(node->right), statement(3)); }
            have node->right == middle by {
                rewrite(node->right, at(before_left, node->right));
                close();
            }
            have pivot->left == node by { normalize(); }
            have separate(statement(3).footprint, memory(pivot->right)) by {
                normalize() using { at(before_left, separate(memory(pivot->right), memory(pivot->left))); };
            }
            have defined(pivot->right) by { preserve(memory(pivot->right), statement(3)); }
            have defined(pivot->left) by { normalize(); }
            have node->left == at(before_left, node->left) by { preserve(memory(node->left), statement(3)); }
            have node->left == old(node->left) by {
                rewrite(node->left, at(before_left, node->left));
                rewrite(at(before_left, node->left), at(before_right, node->left));
                close();
            }
            have node->right == old(node->right->left) by {
                rewrite(node->right, middle);
                close();
            }
            have pivot->right == at(before_left, pivot->right) by { preserve(memory(pivot->right), statement(3)); }
            have pivot->right == old(node->right->right) by {
                rewrite(pivot->right, at(before_left, pivot->right));
                rewrite(at(before_left, pivot->right), at(before_right, pivot->right));
                close();
            }
            let lower = fold(tree_at(node), {
                model: Shape::Node(node, l.model, m.model),
                left: l, right: m
            });
            let rotated = fold(tree_at(pivot), {
                model: Shape::Node(pivot, lower.model, z.model),
                left: lower, right: z
            });
            have shape_left(old(r.model)) == middle_model by {
                rewrite(old(r.model), Shape::Node(pivot_node, middle_model, far_model));
                unfold(shape_left(Shape::Node(pivot_node, middle_model, far_model)));
                normalize();
            }
            have shape_right(old(r.model)) == far_model by {
                rewrite(old(r.model), Shape::Node(pivot_node, middle_model, far_model));
                unfold(shape_right(Shape::Node(pivot_node, middle_model, far_model)));
                normalize();
            }
            step(AugmentRotate, { t: rotated });
            have rotated.model == Shape::Node(old(node->right),
                Shape::Node(node, old(l.model), shape_left(old(r.model))),
                shape_right(old(r.model))) by {
                rewrite(shape_left(old(r.model)), middle_model);
                rewrite(shape_right(old(r.model)), far_model);
                close();
            }
            step();
            close();
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
    have AugmentRotate(&clobber) by { close(); }
    let { rotated: rotated } = step(rotate_left, { l: a, r: b });
}

```

```expect
fail: could not establish `AugmentRotate(&clobber)`
```
