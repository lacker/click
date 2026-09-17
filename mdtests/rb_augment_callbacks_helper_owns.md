# Three callback calls whose contracts own what they write

This is `mdtests/rb_augment_callbacks_helper.md` with the footprints the real
callbacks have: each contract `owns` the link cells it writes rather than
merely viewing them. The C is identical; only the Click changes.

An owned footprint makes every indirect call a checked memory effect, so the
call havocs the cells the callee owns. The next field of the callback table is
read after that havoc, and the contract carried by that field must survive it.
It does, because the helper requires
`separate(memory(object(augment)), memory(object(parent)))`: the table is
provably outside the written range, its cells are retained across the call, and
the load resolves to the same value the `open` named. Dropping that requirement
is what `mdtests/rb_augment_callbacks_helper_owns_rejects_unseparated.md`
checks.

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
    requires separate(memory(object(augment)), memory(object(parent)));
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
