# A `have` goal that reads through an arm binding and calls a pure function

A proof `match` arm binds the constructor's payloads, and a struct-pointer
binding is a memory base (package A5): `id->word` and `p->word` name the same
cell, because the arm's `fact p == id` identifies them. A `have` goal may
write either spelling.

It may write either spelling *or* call a pure function. It may not do both.
`have (p->word & 1) == color_bit(color)` is checked and proved. The same goal
with the arm's own spelling for the same cell,
`have (id->word & 1) == color_bit(color)`, does not reach a proof at all: it
is refused before its body runs, with `the kernel lowering produced 0 paths,
not one`.

The two halves are each fine on their own. `have (id->word & 1) == 1` lowers
(and then fails honestly on the fact it cannot prove), and
`have color_bit(color) == 1` lowers. Only the combination produces no path.

The cause is visible in
`lower_fixed_state_proposition_through_kernel_recording_introductions`: a
proposition that contains a Click function call is lowered under
`keep_spec_loads_symbolic()`, and the symbolic-load path in
`src/kernel/spec.rs` yields no path for a base that is an arm binding rather
than a C local. So the pure call is what switches the load into the mode that
cannot read the binding's cell.

This blocks package C3 of
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md).
The insert fixup's black-parent exit has to bridge the frame's own body fact
`(identity->__rb_parent_color & 1) == color_bit(color)` to the loaded word the
C `if` tests, and every spelling of that bridge is a goal or a `simp` premise
of exactly this shape.

```c filename=arm_binding_load.c
struct node { unsigned long word; struct node *left; };

unsigned long peek_at_the_local(struct node *p) {
    return p->word;
}

unsigned long peek_at_the_binding(struct node *p) {
    return p->word;
}
```

```click
verifying "arm_binding_load.c";

spec enum Color { Red, Black }

function color_bit(color: Color) -> int {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

spec enum Tree {
    Empty,
    Node(struct node*, Color, Tree),
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, color, left_model) => {
            owns p->word;
            owns p->left;
            owns left: tree_at(p->left);
            fact p != 0;
            fact p == id;
            fact (p->word & 1) == color_bit(color);
            fact left.model == left_model;
        },
    }
}

unsigned long peek_at_the_local(struct node* p) {
    consumes t: tree_at(p);
    requires t.model != Tree::Empty;
    produces u: tree_at(p);
    ensures u.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, color, left_model) => {
            unfold(t) as { left: l };
            have (p->word & 1) == color_bit(color) by { simp(); }
            step();
            let u = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                { left: l });
            simp();
        },
    }
}

unsigned long peek_at_the_binding(struct node* p) {
    consumes t: tree_at(p);
    requires t.model != Tree::Empty;
    produces u: tree_at(p);
    ensures u.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, color, left_model) => {
            unfold(t) as { left: l };
            have (id->word & 1) == color_bit(color) by { simp(); }
            step();
            let u = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                { left: l });
            simp();
        },
    }
}
```

```expect
fail: could not lower `have` proposition: the kernel lowering produced 0 paths, not one
```
