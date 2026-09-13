# A `simp() using` premise inside a `have` body cannot name an arm binding

The uniform-scoping slices resolve a proof `match` arm's bindings the way a
`have` goal resolves them: in theorem arguments and `apply ... using` premises,
in `instantiate`, in `extract`
([`theorem_argument_arm_binding.md`](theorem_argument_arm_binding.md)), and in
a `loop` written inside the arm
([`loop_clause_reads_arm_bindings.md`](loop_clause_reads_arm_bindings.md)).

One site was missed: the premises of a `simp() using { ... }` written inside a
`have` body. The goal of that `have` is materialized against the enclosing
proof's lexical bindings before planning —
`substitute_lexical_bindings_in_proposition` in
`src/surface/proof/checked_drivers/tactic_laws.rs`, whose own comment says a
binding "reach[es] it only here" — but the `have`'s *body* is handed to
`plan_smart_have_in_current_state` unmaterialized, and that function lowers
each named premise with `lower_fixed_state_proposition`, which is given no
bindings at all. The arm's name is therefore read as an unbound C variable and
the premise is refused with `` `color` is not an algebraic binding in this
scope ``.

The goal below names `color` and is accepted; the premise beside it names the
same `color` and is not. A premise that is *already* a recorded available fact
is matched by its spelling and never lowered, so the defect only shows on a
premise the planner has to lower — reflexivity is the smallest one, and the
insert fixup's real premise, the frame body fact written at the arm's own
pointer spelling, is another. The fix belongs with the other scoping sites: thread
the enclosing lexical bindings to the premise lowering and substitute there,
leaving the written spelling as what certificates record and expansion prints,
which is how the `loop`-clause site was fixed. The other `using` positions
inside a `have` body should be checked at the same time.

This blocks package C3 of
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md):
the insert fixup's black-parent exit needs `simp() using` to chain the frame's
body fact `(identity->__rb_parent_color & 1) == color_bit(color)` against the
arm's colour, and the premise cannot be written.

```c filename=simp_using_binding.c
struct node { unsigned long word; struct node *left; };

unsigned long peek(struct node *p) {
    return p->word;
}
```

```click
verifying "simp_using_binding.c";

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

unsigned long peek(struct node* p) {
    consumes t: tree_at(p);
    requires t.model != Tree::Empty;
    produces u: tree_at(p);
    ensures u.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, color, left_model) => {
            unfold(t) as { left: l };
            have (p->word & 1) == color_bit(color) by {
                simp() using { color_bit(color) == color_bit(color); }
            }
            step();
            let u = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                { left: l });
            simp();
        },
    }
}
```

```expect
fail: `color` is not an algebraic binding in this scope
```
