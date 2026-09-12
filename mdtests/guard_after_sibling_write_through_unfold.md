# A cell owned through an arm payload keeps its guard fact across a sibling write

This is [`guard_after_sibling_write.md`](guard_after_sibling_write.md)'s C,
verbatim, with one change on the Click side: the cell the guard reads is owned
through an unfolded resource arm — `frame_at`'s `Held` arm owns
`identity->next` through its *pointer payload* and states
`identity->next == child` — instead of through a contract `owns` clause. The
requirement pins the payload to the C parameter `x`, so the exposed cell is
`x->next`.

Naming is atomic across producers, so an `unfold` names the cells it exposes
the way contract lowering does. That projection evaluates the arm's memory
clauses, and a clause written over a constructor binding can only be evaluated
when the selection knows what the binding holds: the arm is selected from a
`Constructor` premise here, so `identity` is `x` and `identity->next` is a cell
the projection can name. Until it substituted those bindings the clause did not
evaluate, the cell stayed unnamed, and the write to `y->tag` — a separate
object, whose separation is a resource fact and not a memory-DAG edge — re-minted
the cell's load identity, leaving the arm's fact about the old one and the guard
undecided:

```text
step() requires exactly one statement successor for `probe_ptr#inline:…`, got 2
undecided condition:
  successor 1: pointer-offset equality is true
  successor 2: pointer-offset equality is false
```

This is gap 43 in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md),
and it is what the non-root frames of
[`rb_replace_node.md`](rb_replace_node.md) were waiting for: the verbatim
`rb_replace_node` copies `*new = *victim` and only then reaches
`__rb_change_child`'s `parent->rb_left == old`, whose cell the `ctx_at` frame
owns through its own `identity` payload.

```c filename=unfold_sibling_write.c
struct link {
    struct link *next;
    int32 tag;
};

static inline void probe_ptr(struct link *x, struct link *y, struct link *z, int32 *out) {
    y->tag = 7;
    if (x->next == z)
        out[0] = 1;
    else
        out[0] = 2;
}

void run_frame(struct link *x, struct link *y, struct link *z, int32 *out) {
    probe_ptr(x, y, z, out);
}
```

```click
verifying "unfold_sibling_write.c";

spec enum Frame {
    Top,
    Held(struct link*, int),
}

resource frame_at(child: struct link*) {
    field model: Frame;
    match model {
        Frame::Top => { fact child == 0; },
        Frame::Held(identity, v) => {
            owns identity->next;
            fact identity != 0;
            fact identity->next == child;
        },
    }
}

void run_frame(struct link* x, struct link* y, struct link* z, int32* out) {
    consumes f: frame_at(z);
    owns y->tag;
    owns out[0..1];
    requires f.model == Frame::Held(x, 5);
    produces g: frame_at(z);
    ensures out[0] == 1;
} by {
    unfold(f);
    have x->next == z by { assumption(); }
    execute();
    let g = fold(frame_at(z), { model: old(f.model) }, {});
    simp();
}
```

```expect
pass
```
