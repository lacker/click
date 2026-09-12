# An arm's unwritten-cell fact survives a sibling write

A proof `match` arm owns two cells of the same node and states a fact about
each. The C writes only one of them, and the arm refolds the frame with the
other fact unchanged.

The fact that must survive is about an `unsigned long` cell, which is the
rbtree's packed parent word. A load names its cell and the snapshot of the
cell's last write (`docs/internals/canonicalization.md`), so the value read
before the write and the value read after it are one term: the store is to a
disjoint cell of the same node, and the epoch walk crosses it. Without that
naming the fold would compare a load over the post-write snapshot with a fact
stated over the pre-write one and refuse the refold.

`change_child_requires` states the same proof with the arm selected by a
contract requirement instead of a proof `match`. Both spellings must accept
it, and for the same reason.

```c filename=arm_sibling_write.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};

struct rb_root {
    struct rb_node *rb_node;
};

void change_child_match(struct rb_node *old_child, struct rb_node *new_child,
                        struct rb_node *parent, struct rb_root *root) {
    if (parent)
        parent->rb_left = new_child;
    else
        root->rb_node = new_child;
}

void change_child_requires(struct rb_node *old_child, struct rb_node *new_child,
                           struct rb_node *parent, struct rb_root *root) {
    if (parent)
        parent->rb_left = new_child;
    else
        root->rb_node = new_child;
}
```

```click
verifying "arm_sibling_write.c";

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

void change_child_match(struct rb_node* old_child, struct rb_node* new_child,
                        struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(old_child, parent, root);
    produces d: ctx_at(new_child, parent, root);
    ensures d.model == old(c.model);
} by {
    match c.model {
        Ctx::Top => {
            unfold(c);
            execute();
            let d = fold(ctx_at(new_child, parent, root), { model: Ctx::Top }, {});
            simp();
        },
        Ctx::Left => {
            unfold(c);
            execute();
            let d = fold(ctx_at(new_child, parent, root), { model: Ctx::Left }, {});
            simp();
        },
    }
}

void change_child_requires(struct rb_node* old_child, struct rb_node* new_child,
                           struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(old_child, parent, root);
    requires c.model == Ctx::Left;
    produces d: ctx_at(new_child, parent, root);
    ensures d.model == old(c.model);
} by {
    unfold(c);
    execute();
    let d = fold(ctx_at(new_child, parent, root), { model: Ctx::Left }, {});
    simp();
}
```

```expect
pass
```
