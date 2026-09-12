# An arm's fact the write invalidates still fails at the fold

The mirror of `proof_match_arm_fact_survives_sibling_write.md`: here the C
writes the very cell the arm's surviving fact is about, storing a value the
proof cannot pin. Naming a load by its cell's epoch carries a fact across a
write to a *different* cell; a write to this cell starts a new epoch, so the
refold has no fact for the proposed model and is refused.

```c filename=arm_written_cell.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};

struct rb_root {
    struct rb_node *rb_node;
};

void recolor(struct rb_node *child, unsigned long color,
             struct rb_node *parent, struct rb_root *root) {
    if (parent)
        parent->__rb_parent_color = color;
    else
        root->rb_node = child;
}
```

```click
verifying "arm_written_cell.c";

spec enum Ctx { Top, Left }

resource ctx_at(child: struct rb_node*, parent: struct rb_node*,
                root: struct rb_root*) {
    field model: Ctx;
    match model {
        Ctx::Top => {
            owns root->rb_node;
            fact root != 0;
            fact parent == 0;
            fact root->rb_node == child;
        },
        Ctx::Left => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            fact parent != 0;
            fact parent->rb_left == child;
            fact parent->__rb_parent_color == 1;
        },
    }
}

void recolor(struct rb_node* child, uint64 color, struct rb_node* parent,
             struct rb_root* root) {
    consumes c: ctx_at(child, parent, root);
    produces d: ctx_at(child, parent, root);
    ensures d.model == old(c.model);
} by {
    match c.model {
        Ctx::Top => {
            unfold(c);
            execute();
            let d = fold(ctx_at(child, parent, root), { model: Ctx::Top }, {});
            simp();
        },
        Ctx::Left => {
            unfold(c);
            execute();
            let d = fold(ctx_at(child, parent, root), { model: Ctx::Left }, {});
            simp();
        },
    }
}
```

```expect
fail: fold requires the instance body facts for the proposed fields
```
