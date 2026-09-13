# A consumed instance's arm equation is cited at entry once it is unfolded

A proof `match` on a consumed instance's model records the arm's constructor
equation with its written spelling, `t.model == Tree::Node(id, color,
left_model)`. That spelling names the instance at unchanged function entry.
Once the arm has unfolded `t` and folded the produced instance under another
name, `t.model` names nothing at all in the arm's later states: `t` was
consumed and never refolded.

The closing `simp()` here proves `u.model == old(t.model)` from the arm's
equation. The proof verified, but its expansion cited the equation by the
written spelling, and rechecking the certificate then failed to lower that
`rewrite` with `the kernel lowering hit Paths`, so `click audit` disagreed
with `click verify`. The certificate lookup accepted the recorded pair
whenever the spelling had no lowering at all, on the reasoning that the pair
was all there was to go on; for a constructor equation that acceptance cited
a spelling the recheck cannot read. A constructor equation whose written
spelling no longer lowers is now cited in its entry-anchored form,
`old(t.model) == Tree::Node(id, color, left_model)`, which is what the
expansion prints and what the recheck lowers to the same fact. The same file
written with `owns t` and a refold under the same name never had the
problem, because `t.model` then names the refolded instance and the lookup
already re-lowered it.

`src/surface/tests/expansion_tests.rs` expands the `simp()` site of this
fixture and reverifies the result; the mdtest gate checks verification only.

```c filename=consumed_arm.c
struct node { unsigned long word; struct node *left; };

unsigned long peek(struct node *p) {
    return p->word;
}
```

```click
verifying "consumed_arm.c";

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
            step();
            let u = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                { left: l });
            simp();
        },
    }
}
```

```expect
pass
```
