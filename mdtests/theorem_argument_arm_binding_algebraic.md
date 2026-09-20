# An ADT-typed arm binding is a theorem argument

The algebraic half of
[`theorem_argument_arm_binding.md`](theorem_argument_arm_binding.md): the same
proof `match` arm, and theorems applied both at the bare `Tree`-typed binding
`left_model` and at a constructor built from the arm's bindings. The binding
lowers as the symbolic model value the arm introduced, so the theorem's
conclusion is stated about that value and closes the `have`.

```c filename=arm_binding_algebraic.c
struct node { int value; struct node *left; };

int peek(struct node *p) {
    return p->value;
}
```

```click
verifying "arm_binding_algebraic.c";

spec enum Tree {
    Empty,
    Node(struct node*, int, Tree),
}

function depth_ok(t: Tree) -> int32 {
    match t {
        Tree::Empty => 1,
        Tree::Node(id, value, left) => 1,
    }
}

theorem depth_ok_of(t: Tree) {
    ensures depth_ok(t) == 1 by {
        induct(t) as ih {
            Tree::Empty => {
                unfold(depth_ok(Tree::Empty));
                normalize();
            }
            Tree::Node(id, value, left) => {
                unfold(depth_ok(Tree::Node(id, value, left)));
                normalize();
            }
        }
    }
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, value, left_model) => {
            owns p->value;
            owns p->left;
            owns left: tree_at(p->left);
            fact p != 0;
            fact p == id;
            fact p->value == value;
            fact left.model == left_model;
        },
    }
}

int peek(struct node* p) {
    consumes t: tree_at(p);
    requires t.model != Tree::Empty;
    produces u: tree_at(p);
    ensures depth_ok(u.model) == 1;
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, value, left_model) => {
            let { left: l } = unfold(t);
            step();
            have depth_ok(left_model) == 1 by {
                apply(depth_ok_of(left_model));
                assumption();
            }
            have depth_ok(Tree::Node(id, value, left_model)) == 1 by {
                apply(depth_ok_of(Tree::Node(id, value, left_model)));
                assumption();
            }
            let u = fold(tree_at(p), { model: Tree::Node(id, value, left_model) },
                         { left: l });
            simp();
        },
    }
}
```

```expect
pass
```
