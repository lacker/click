# A rotation callback preserves the modeled shape of the tree it is handed

This is `mdtests/augment_rotate_callback.md` again, with the memory-only
`shape` resource replaced by an algebraic model. `tree_at` owns the two link
cells and carries a `Shape` model of the links alone; the `augmented` cells
stay outside it, exactly as in the memory-only fixture, so a callback can
update the augmentation while the tree it was handed is only its to preserve,
not to rewire.

The callback contract therefore takes the rebuilt tree as a proof parameter and
promises its model back unchanged:

```
contract AugmentRotate(t: tree_at(new)) for void(struct node* old, struct node* new)
```

The rotation helper still takes the root's two link cells and the two subtree
resources rather than one folded `tree_at(node)`, as the memory-only fixture
does: a contract cannot today own a memory segment, here
`node->right->augmented`, whose base is loaded through a field owned by another
owned or consumed composite in the same contract.

`bump` and `reset` state model preservation in their own contracts — a
callee's post instance fields are always fresh, so preservation that is not
stated is not available — and then form `AugmentRotate(&bump)` and
`AugmentRotate(&reset)` automatically at the call site, with no execution
theorem: each implementation declares exactly one `tree_at` binder with the
same argument as the contract's one proof parameter, so the binding is forced.

The model guarantee is load-bearing rather than decorative: `rotate_left`
states the whole rotated model, `Shape::Node(pivot, Shape::Node(node, left,
middle), far)`, and that guarantee survives the indirect call only because
`AugmentRotate` returns `t.model` unchanged. `rotate_bump` and `rotate_reset`
carry the same statement across an ordinary C call, binding the helper's two
consumed subtrees and its produced result through the call's binder map.

Two proof-shaping notes. The equations that unfold `shape_left` and
`shape_right` are proved before the callback call, but the model equation
itself has to be restated after it: the callee returns fresh instance fields
tied to the entry fields only by `t.model == old(t.model)`, and the closing
`simp()` does not orient the two `shape_*` equations on its own, so the `have`
after the call supplies them with explicit `rewrite`s.

```c filename=augment_rotate_model.c
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

struct node *rotate_bump(struct node *node) {
    return rotate_left(node, &bump);
}

struct node *rotate_reset(struct node *node) {
    return rotate_left(node, &reset);
}
```

```click
verifying "augment_rotate_model.c";

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

void bump(struct node* old, struct node* new) {
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
} by {
    execute();
    simp();
}

void reset(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    owns t: tree_at(new);
    owns old->augmented;
    owns new->augmented;
    ensures t.model == old(t.model);
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

struct node* rotate_bump(struct node* node) {
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
    let rotated = step(rotate_left(node, &bump), { l: a, r: b });
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
pass
```
