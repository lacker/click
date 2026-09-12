# A pure function's match arm does not capture a substituted name

`unfold(f(args))` instantiates `f`'s body by substituting the arguments for the
parameters and then reducing the body's `match` at the constructor. Both stages
replace names, so an argument mentioning a name the body's arm *binds* used to
be rebound to that arm's payload: the instantiated body said something other
than the definition, and the meaning of a pure function depended on what the
caller happened to call its variables.

That was unsound. Here `reparent`'s `Node` arm binds a payload named `parent`
and the C function has a parameter named `parent`, so
`unfold(reparent(RbTree::Node(node, node, Red, Empty, Empty), parent))` produced
the *old* parent, `RbTree::Node(node, node, Red, Empty, Empty)`, and
`normalize()` closed that false equation under `requires node != parent`.

Substitution now renames a match-arm binding out of the way before a
replacement that mentions it reaches the arm body — the rule quantifier and
range-fold binders already follow (`prepare_contract_expression_binding_body` in
`src/surface/lowering/contract_substitution.rs`) — and refuses if a rename
cannot separate them. The captured equation no longer closes; the true one
does, in
[`spec_function_arm_binding_capture_renames.md`](spec_function_arm_binding_capture_renames.md).

```c filename=capture.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};

int probe(struct rb_node *node, struct rb_node *parent) {
    return 0;
}
```

```click
verifying "capture.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

function reparent(tree: RbTree, fresh: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) =>
            RbTree::Node(identity, fresh, color, left, right),
    }
}

int probe(struct rb_node* node, struct rb_node* parent) {
    requires node != parent;
    ensures result == 0;
} by {
    have reparent(
            RbTree::Node(node, node, Color::Red, RbTree::Empty, RbTree::Empty), parent)
        == RbTree::Node(node, node, Color::Red, RbTree::Empty, RbTree::Empty) by {
        unfold(reparent(
            RbTree::Node(node, node, Color::Red, RbTree::Empty, RbTree::Empty), parent));
        normalize();
    }
    execute();
    simp();
}
```

```expect
fail: `normalize` goal did not normalize to true
```
