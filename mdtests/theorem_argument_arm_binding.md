# A theorem argument may be a proof `match` arm binding

A proof `match` on an instance's model binds the constructor's payloads, and
the C proof needs those names wherever it writes a term: in a `have` goal,
and equally as the arguments of a theorem it applies inside that `have`. The
pure library's frame-level theorems are stated over exactly such payloads, so
a fixup step's `have` is "apply the case theorem at the arm's bindings".

Every position that takes a written theorem application resolves it the way
a `have` goal is resolved: goal binders first, then the proof locals that a
match arm, a `let { ... } = unfold(...)`, a `let ... = step(...)`, or a loop binder
introduced. Here the pointer binding `id`, the integer binding `value`, and
the model binding `left_model` are all theorem arguments. Before this rule
the pointer and integer bindings lowered to no path at all, and the model
binding was refused as not in scope; the companion
[`theorem_argument_arm_binding_algebraic.md`](theorem_argument_arm_binding_algebraic.md)
pins the algebraic case on its own.

```c filename=arm_binding.c
struct node { int value; struct node *left; };

int peek(struct node *p) {
    return p->value;
}
```

```click
verifying "arm_binding.c";

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

theorem depth_ok_node(id: struct node*, value: int, left: Tree) {
    ensures depth_ok(Tree::Node(id, value, left)) == 1 by {
        unfold(depth_ok(Tree::Node(id, value, left)));
        normalize();
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
            have depth_ok(Tree::Node(id, value, left_model)) == 1 by {
                apply(depth_ok_node(id, value, left_model));
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
