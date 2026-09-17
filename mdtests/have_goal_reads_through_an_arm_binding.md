# A `have` goal that reads through an arm binding and calls a pure function

A proof `match` arm binds the constructor's payloads, and a struct-pointer
binding is a memory base (package A5): `id->word` and `p->word` name the same
cell, because the arm's `fact p == id` identifies them. A `have` goal may
write either spelling, including a goal that also calls a pure function.

`have (p->word & 1) == color_bit(color)` and
`have (id->word & 1) == color_bit(color)` are the same goal written two ways,
and both are checked and proved here. The third function writes the second
spelling inside a loop's `preserve` body, which is where a recursive-structure
proof actually needs it: the arm is entered once per iteration and the goal
bridges the resource's own body fact to the loaded word.

A proof arm's bindings previously carried no declared type, so `id->word`
resolved against no struct layout and lowered as a width-unknown load. On its
own that silently read a four-byte cell instead of the owned eight-byte one
and then failed honestly; combined with a pure call, which lowers the
proposition with its spec loads kept symbolic, the mismatched width produced no
path at all and the goal was refused before its body ran. A proof arm now types
its bindings from the datatype exactly as a resource arm does, so
`id->word` resolves against `struct node` and reads the cell the arm's
equation names.

```c filename=arm_binding_load.c
struct node { unsigned long word; struct node *left; };

unsigned long peek_at_the_local(struct node *p) {
    return p->word;
}

unsigned long peek_at_the_binding(struct node *p) {
    return p->word;
}

unsigned long spin_over_the_binding(struct node *p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
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
    owns t: tree_at(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, color, left_model) => {
            unfold(t) as { left: l };
            have (p->word & 1) == color_bit(color) by { simp(); }
            step();
            let t = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                { left: l });
            simp();
        },
    }
}

unsigned long peek_at_the_binding(struct node* p) {
    owns t: tree_at(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, color, left_model) => {
            unfold(t) as { left: l };
            have (id->word & 1) == color_bit(color) by { simp(); }
            step();
            let t = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                { left: l });
            simp();
        },
    }
}

unsigned long spin_over_the_binding(struct node* p, int32 n) {
    requires n >= 0;
    owns t: tree_at(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    step();
    step();
    loop {
        owns t: tree_at(p);
        invariant i >= 0;
        invariant i <= n;
        invariant t.model == old(t.model);
        invariant t.model != Tree::Empty;

        initialize by simp;
        preserve by {
            match t.model {
                Tree::Empty => { contradiction(t.model == Tree::Empty); },
                Tree::Node(id, color, left_model) => {
                    have Tree::Node(id, color, left_model) == old(t.model) by {
                        simp() using { t.model == Tree::Node(id, color, left_model);
                            t.model == old(t.model); }
                    }
                    unfold(t) as { left: l };
                    have (id->word & 1) == color_bit(color) by { simp(); }
                    step();
                    let t = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                        { left: l });
                    close_invariants();
                },
            }
        }
    }
    step();
    simp();
}
```

```termination
pending: unranked loop
```

```expect
pass
```
