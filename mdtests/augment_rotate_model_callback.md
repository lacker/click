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

The rotation helper consumes one folded `tree_at(node)`, exactly as the
memory-only fixture consumes one folded `shape(node)`. `tree_at` decides which
links it owns from its `model` field, and a contract is lowered before any
proof step runs, so `owns node->right->augmented` can only address its cell if
the contract itself settles the arm. `requires t.model != Shape::Empty` does:
`Shape` has two constructors, so ruling `Empty` out leaves `Shape::Node`, and
the `Node` arm's `node->left` and `node->right` become readable while
`tree_at(node)` stays folded. A resource clause also reads cells the rest of
its contract supplies, which `mdtests/contract_owns_through_composite_field.md`
pins; here both rules are needed at once.

The second requirement, `shape_right(t.model) != Shape::Empty`, is the old
`r.model != Shape::Empty` written against the whole tree's model: with no
separate binder for the right subtree, the model function names it. It does not
select an arm of `tree_at(node)` — it is a premise about a different value — and
the proof uses it to close the `Shape::Empty` case of the inner constructor
match.

`bump` and `reset` state model preservation in their own contracts — a
callee's post instance fields are always fresh, so preservation that is not
stated is not available — and then form `AugmentRotate(&bump)` and
`AugmentRotate(&reset)` automatically at the call site, with no execution
theorem: each implementation declares exactly one `tree_at` binder with the
same argument as the contract's one proof parameter, so the binding is forced.

The model guarantee is load-bearing rather than decorative: `rotate_left`
states the whole rotated model, `Shape::Node(pivot, Shape::Node(node, left,
middle), far)`, entirely in `shape_left` and `shape_right` applied to
`old(t.model)`, and that guarantee survives the indirect call only because
`AugmentRotate` returns `t.model` unchanged. `rotate_bump` and `rotate_reset`
carry the same statement across an ordinary C call, binding the helper's one
consumed tree and its produced result through the call's binder map.

Two proof-shaping notes. Both constructor matches run at the unchanged function
entry, before anything is unfolded, because that is where the `match` tactic
introduces cases; the two `unfold`s then follow inside the innermost arm. The
equations that unfold `shape_left` and `shape_right` are proved before the
callback call, but the model equation itself has to be restated after it: the
callee returns fresh instance fields tied to the entry fields only by
`t.model == old(t.model)`. The closing `simp()` orients the retained `shape_*`
equations through the returned constructor, so the `have` after the call needs
no explicit rewrites.

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
    consumes t: tree_at(node);
    requires t.model != Shape::Empty;
    requires shape_right(t.model) != Shape::Empty;
    owns node->augmented;
    owns node->right->augmented;
    produces r: tree_at(result);

    ensures result == old(node->right);
    ensures r.model == Shape::Node(old(node->right),
        Shape::Node(node, shape_left(old(t.model)),
            shape_left(shape_right(old(t.model)))),
        shape_right(shape_right(old(t.model))));
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    match t.model {
        Shape::Empty => { contradiction(t.model == Shape::Empty); },
        Shape::Node(root_node, left_model, right_model) => {
            have shape_left(old(t.model)) == left_model by {
                rewrite(old(t.model) == Shape::Node(root_node, left_model, right_model));
                unfold(shape_left(Shape::Node(root_node, left_model, right_model)));
                normalize();
            }
            have shape_right(old(t.model)) == right_model by {
                rewrite(old(t.model) == Shape::Node(root_node, left_model, right_model));
                unfold(shape_right(Shape::Node(root_node, left_model, right_model)));
                normalize();
            }
            have right_model != Shape::Empty by { simp(); }
            match right_model {
                Shape::Empty => { contradiction(right_model == Shape::Empty); },
                Shape::Node(pivot_node, middle_model, far_model) => {
                    have shape_left(shape_right(old(t.model))) == middle_model by {
                        rewrite(shape_right(old(t.model)) == right_model);
                        rewrite(right_model == Shape::Node(pivot_node, middle_model, far_model));
                        unfold(shape_left(Shape::Node(pivot_node, middle_model, far_model)));
                        normalize();
                    }
                    have shape_right(shape_right(old(t.model))) == far_model by {
                        rewrite(shape_right(old(t.model)) == right_model);
                        rewrite(right_model == Shape::Node(pivot_node, middle_model, far_model));
                        unfold(shape_right(Shape::Node(pivot_node, middle_model, far_model)));
                        normalize();
                    }
                    unfold(t) as { left: l, right: rs };
                    unfold(rs) as { left: m, right: z };
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    let lower = fold(tree_at(node), {
                        model: Shape::Node(node, l.model, m.model)
                    }, { left: l, right: m });
                    let r = fold(tree_at(pivot), {
                        model: Shape::Node(pivot, lower.model, z.model)
                    }, { left: lower, right: z });
                    step(AugmentRotate(r));
                    have r.model == Shape::Node(old(node->right),
                        Shape::Node(node, shape_left(old(t.model)),
                            shape_left(shape_right(old(t.model)))),
                        shape_right(shape_right(old(t.model)))) by {
                        simp();
                    }
                    step();
                    simp();
                },
            }
        },
    }
}

struct node* rotate_bump(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes a: tree_at(node);
    requires a.model != Shape::Empty;
    requires shape_right(a.model) != Shape::Empty;
    owns node->augmented;
    owns node->right->augmented;
    produces rotated: tree_at(result);

    ensures result == old(node->right);
    ensures rotated.model == Shape::Node(old(node->right),
        Shape::Node(node, shape_left(old(a.model)),
            shape_left(shape_right(old(a.model)))),
        shape_right(shape_right(old(a.model))));
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    let rotated = step(rotate_left(node, &bump), { t: a });
    execute();
    simp();
}

struct node* rotate_reset(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes a: tree_at(node);
    requires a.model != Shape::Empty;
    requires shape_right(a.model) != Shape::Empty;
    owns node->augmented;
    owns node->right->augmented;
    produces rotated: tree_at(result);

    ensures result == old(node->right);
    ensures rotated.model == Shape::Node(old(node->right),
        Shape::Node(node, shape_left(old(a.model)),
            shape_left(shape_right(old(a.model)))),
        shape_right(shape_right(old(a.model))));
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    let rotated = step(rotate_left(node, &reset), { t: a });
    execute();
    simp();
}
```

```expect
pass
```
