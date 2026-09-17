# Cell-level separation is enough for the owned callback footprints

`mdtests/rb_augment_callbacks_helper_owns.md` separates the whole callback
table from the whole node. The helper does not need that much: the only table
cells read after a call are the two fields the helper has not dispatched yet,
and the only cell any of the three callbacks writes is `parent->left`.
Naming those two pairs is enough, and it says exactly which overlaps would
break the proof.

The C is identical to `mdtests/rb_augment_callbacks_helper.md`; only the
requirements change.

```c filename=rb_augment_callbacks.c
struct node {
    struct node *left;
    struct node *right;
};

struct rb_augment_callbacks {
    void (*propagate)(struct node *node, struct node *stop);
    void (*copy)(struct node *old, struct node *new);
    void (*rotate)(struct node *old, struct node *new);
};

void dummy_propagate(struct node *node, struct node *stop) { }

void dummy_copy(struct node *old, struct node *new) { }

void dummy_rotate(struct node *old, struct node *new) { }

static const struct rb_augment_callbacks dummy_callbacks = {
    .propagate = dummy_propagate,
    .copy = dummy_copy,
    .rotate = dummy_rotate
};

void erase_augmented(struct node *node, struct node *parent,
                     const struct rb_augment_callbacks *augment) {
    augment->propagate(parent, 0);
    augment->copy(node, parent);
    augment->rotate(node, parent);
}

void erase_dummy(struct node *node, struct node *parent) {
    erase_augmented(node, parent, &dummy_callbacks);
}
```

```click
verifying "rb_augment_callbacks.c";

contract void Propagate(struct node* node, struct node* stop) {
    requires node != 0;
    owns node->left;
    ensures node->left == old(node->left);
}

contract void Copy(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    owns new->left;
    ensures new->left == old(new->left);
}

contract void Rotate(struct node* old, struct node* new) {
    requires new != 0;
    owns new->left;
    owns new->right;
    ensures new->left == old(new->left);
    ensures new->right == old(new->right);
}

resource callback_suite(augment: const struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact Propagate(augment->propagate);
    fact Copy(augment->copy);
    fact Rotate(augment->rotate);
}

void erase_augmented(struct node* node, struct node* parent,
                     const struct rb_augment_callbacks* augment) {
    views callback_suite(augment);
    requires node != 0;
    requires parent != 0;
    requires separate(memory(augment->copy), memory(parent->left));
    requires separate(memory(augment->rotate), memory(parent->left));
    owns parent->left;
    owns parent->right;
    ensures parent->left == old(parent->left);
    ensures parent->right == old(parent->right);
} by {
    open(callback_suite(augment)) {
        execute();
        simp();
    }
}
```

```expect
pass
```
