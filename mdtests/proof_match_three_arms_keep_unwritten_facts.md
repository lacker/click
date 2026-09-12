# Three frame arms each keep their unwritten-cell fact

The three-constructor form of `proof_match_arm_fact_survives_sibling_write.md`:
a wider proof `match` splits the execution frontier once per constructor, and
each of the three arms refolds a frame whose packed parent word the C never
wrote.

The two non-`Top` frames differ only in that word's colour bit, so nothing but
the arm's own fact distinguishes them, and an arm that lost the fact across the
sibling write could not refold its own constructor.

```c filename=three_frames.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};

struct rb_root {
    struct rb_node *rb_node;
};

void change_child(struct rb_node *old_child, struct rb_node *new_child,
                  struct rb_node *parent, struct rb_root *root) {
    if (parent)
        parent->rb_left = new_child;
    else
        root->rb_node = new_child;
}
```

```click
verifying "three_frames.c";

spec enum Frame { Top, RedParent, BlackParent }

resource ctx_at(child: struct rb_node*, parent: struct rb_node*,
                root: struct rb_root*) {
    field model: Frame;
    match model {
        Frame::Top => {
            owns root->rb_node;
            fact root != 0;
            fact parent == 0;
            fact root->rb_node == child;
        },
        Frame::RedParent => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            fact parent != 0;
            fact parent->rb_left == child;
            fact parent->__rb_parent_color == 0;
        },
        Frame::BlackParent => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            fact parent != 0;
            fact parent->rb_left == child;
            fact parent->__rb_parent_color == 1;
        },
    }
}

void change_child(struct rb_node* old_child, struct rb_node* new_child,
                  struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(old_child, parent, root);
    produces d: ctx_at(new_child, parent, root);
    ensures d.model == old(c.model);
} by {
    match c.model {
        Frame::Top => {
            unfold(c);
            execute();
            let d = fold(ctx_at(new_child, parent, root), { model: Frame::Top }, {});
            simp();
        },
        Frame::RedParent => {
            unfold(c);
            execute();
            let d = fold(ctx_at(new_child, parent, root), { model: Frame::RedParent }, {});
            simp();
        },
        Frame::BlackParent => {
            unfold(c);
            execute();
            let d = fold(ctx_at(new_child, parent, root), { model: Frame::BlackParent }, {});
            simp();
        },
    }
}
```

```expect
pass
```
