# a model payload takes the null pointer constant

`detach` writes a null parent word and refolds its modelled instance with the
model that says so, `Tree::Node(identity, 0, value)`. `0` in a pointer-typed
payload is the C null-pointer-constant rule that
[`rb_pure_null_pointer_argument.md`](rb_pure_null_pointer_argument.md) already
applies to a resource argument and to a pure call's argument. It reaches the
payload too: without the field's declared type the literal lowered as an
`int32` zero and the whole constructor denoted no value, so the fold was
refused with `fold field \`model\`: algebraic initializer must denote one
symbolic value`.

The root-blackening exit of the Linux insert fixup is this shape.
`rb_set_parent_color(node, NULL, RB_BLACK)` makes the inserted node the tree's
root, and the model that describes the result is
`RbTree::Node(node, 0, Color::Black, left, right)`; there is no C name for that
null, and writing the root case out as its own model would be a second model.

```c filename=detach.c
struct node {
    struct node *parent;
    int value;
};

void detach(struct node *n)
{
    n->parent = 0;
}
```

```click
verifying "detach.c";

spec enum Tree {
    Empty,
    Node(struct node*, struct node*, int),
}

function is_root(t: Tree) -> int32 {
    match t {
        Tree::Empty => 0,
        Tree::Node(identity, parent, value) => if parent == 0 { 1 } else { 0 },
    }
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(identity, parent, value) => {
            owns p->parent;
            owns p->value;
            fact p != 0;
            fact p == identity;
            fact p->parent == parent;
            fact p->value == value;
        },
    }
}

void detach(struct node* n) {
    consumes t: tree_at(n);
    requires t.model != Tree::Empty;
    produces u: tree_at(n);
    ensures is_root(u.model) == 1;
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(identity, node_parent, value) => {
            unfold(t);
            execute();
            let u = fold(tree_at(n), { model: Tree::Node(identity, 0, value) });
            have is_root(Tree::Node(identity, 0, value)) == 1 by {
                unfold(is_root(Tree::Node(identity, 0, value)));
                normalize();
            }
            have is_root(u.model) == 1 by {
                rewrite(u.model == Tree::Node(identity, 0, value));
                assumption();
            }
            simp();
        },
    }
}
```

```expect
pass
```
