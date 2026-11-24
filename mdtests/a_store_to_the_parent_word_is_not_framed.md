# A store to the parent word itself is not framed

The companion of `a_parent_word_frames_across_a_child_store_in_a_loop.md`.
Here the loop body stores to the parent word itself, so its two 64-bit reads
are different versions of the cell and the same transport is refused.

```c filename=parent_word_store.c
#define WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};
void rotate_child_link(struct rb_node *gparent, struct rb_node *tmp) {
    struct rb_node *parent = gparent->rb_left;
    while (1) {
        WRITE_ONCE(parent->__rb_parent_color, 1);
        break;
    }
}
```

```click
verifying "parent_word_store.c";
resource node_at(p: struct rb_node*) {
    field v: int32;
    fact p != 0;
    owns p->__rb_parent_color;
    owns p->rb_right;
    owns p->rb_left;
}
resource left_child(g: struct rb_node*) {
    field v: int32;
    owns g->rb_left;
    owns child: node_at(g->rb_left);
    fact child.v == v;
}
void rotate_child_link(struct rb_node* gparent, struct rb_node* tmp) {
    owns s: left_child(gparent);
} by {
    step_until(loop(0).entry);
    loop {
        owns s: left_child(gparent);
        invariant parent == gparent->rb_left;
        invariant parent == old(gparent->rb_left);
        decreases 0;
        initialize by close();
        maintain by {
            let { child: c } = unfold(s);
            unfold(c);
            mark before_store;
            step();
            have parent->__rb_parent_color == at(before_store, parent->__rb_parent_color) by {
                close();
            }
            let c = fold(node_at(gparent->rb_left), { v: 0 });
            let s = fold(left_child(gparent), { v: 0, child: c });
            step();
        }
    }
}
```

```expect
fail: `solve` failed
```
