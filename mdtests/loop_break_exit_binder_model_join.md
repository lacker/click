# `break` exits join through the loop's binders

`paint` is the shape of Linux's `__rb_insert`: `while (true)`, every way out a
`break`, and each `break` writes a colour and refolds the loop's modelled
instance before leaving. The two exits therefore stand at different states —
different models for `c`, different bytes in `p->shade` — which is what A23's
rule refused.

The loop rule now describes the one successor the way decision D5 describes an
arbitrary visit. The declared binder `c` is rebound at each exit by family and
argument equality, whatever the body called it, and given a fresh model exactly
as the loop head does; the cell the exits wrote differently is given a fresh
value; and each exit contributes, as its own disjunct, the equations pinning
those fresh names to what that exit actually reached. Nothing is assumed of an
exit that did not state it: each disjunct is that path's own description of the
successor, so the join is the standard weakening.

The exported disjunction is what the post-loop claim is proved from. `cases`
splits on it and each side reads its own model off its disjunct.

Every path out of the body is a `break`, so the back edge is unreachable and
the constant `decreases 0;` is all the loop's ranking needs: the nonnegativity
member holds and no decrease is ever demanded.

A loop that declares no binder has nothing to read a differing cell back
through, and is refused by name; see
[`loop_break_exit_unowned_cell_rejected.md`](loop_break_exit_unowned_cell_rejected.md).
An exit that does not hold an instance for a declared binder is refused by
name too; see
[`loop_break_exit_missing_binder_rejected.md`](loop_break_exit_missing_binder_rejected.md).

```c filename=paint_node.c
struct node { int32 shade; };

void paint(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            p->shade = 0;
            break;
        } else {
            p->shade = 1;
            break;
        }
    }
}
```

```click
verifying "paint_node.c";

spec enum Color { Red, Black }

resource painted(p: struct node*) {
    field color: Color;
    match color {
        Color::Red => { owns p->shade; fact p->shade == 0; },
        Color::Black => { owns p->shade; fact p->shade == 1; },
    }
}

void paint(struct node* p, int32 flag) {
    owns c: painted(p);
    requires c.color == Color::Black;
    ensures c.color == Color::Red or c.color == Color::Black;
} by {
    loop {
        decreases 0;
        owns c: painted(p);
        invariant c.color == Color::Black;

        preserve by {
            unfold(c);
            if flag == 0 {
                step();
                step();
                let c = fold(painted(p), { color: Color::Red });
                step();
            } else {
                step();
                step();
                let c = fold(painted(p), { color: Color::Black });
                step();
            }
        }
    }
    step();
    have c.color == Color::Red or c.color == Color::Black by {
        cases((flag == 0 and c.color == Color::Red and p->shade == 0) or (c.color == Color::Black and p->shade == 1)) {
            simp();
        } {
            simp();
        }
    }
    simp();
}
```

```expect
pass
```
