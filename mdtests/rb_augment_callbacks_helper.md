# An erase helper calls three abstract augmentation callbacks

`erase_augmented` mirrors the shape of Linux's erase path: it takes a
`const struct rb_augment_callbacks *` and calls `propagate`, `copy` and
`rotate` through it. Here the helper is verified alone, against three abstract
facts and nothing else. The `callback_suite` resource carries one named
contract per field, the helper only `views` it, and `open` brings the three
facts into scope for the three indirect calls. Nothing enumerates the
callbacks: each call is justified by the contract on that field alone.

The three contracts are deliberately different, so binding a field to the
wrong function is a proof failure rather than a signature coincidence:
`Propagate` works on its first argument's left link, `Copy` on its second
argument's left link, and `Rotate` on both links of its second argument.
`mdtests/rb_augment_callbacks_table.md` binds the three fields to the three
no-op helpers through a `const` table, and
`mdtests/rb_augment_callbacks_rejects_mismatch.md` binds `.rotate` to a
function that satisfies `Copy` and is refused.

The helper needs `separate(memory(object(augment)), memory(object(parent)))`:
without it the table is allowed to overlap the node the callbacks touch, and
reloading the next field after a call yields a function pointer that carries no
contract.

The three contracts state `views` footprints, which is what the no-op bodies
do. `mdtests/rb_augment_callbacks_helper_owns.md` is this same helper with
`owns` footprints, which is what a real augmentation callback needs: each call
then havocs the link cells it owns, and the separation hypothesis above is what
keeps the table's remaining fields — and the contracts they carry — alive
across the call. `mdtests/rb_augment_callbacks_helper_owns_cell_separate.md`
states that separation cell by cell instead, and
`mdtests/rb_augment_callbacks_helper_owns_rejects_unseparated.md` drops it and
fails at the second call.

Inside `lib/rbtree.c` itself only the exported, non-inline entry points need a
contract like this. The always-inline `__rb_insert` takes its `augment_rotate`
as a parameter too, but every caller inlines it with a concrete callback, so
each indirect call there is resolved at the call site and no named contract is
required; `__rb_erase_color` and `__rb_insert_augmented`, which are compiled
once and called through the exported symbol, are the ones that need
`AugmentRotate(augment_rotate)` and this suite.

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
    views node->left;
    ensures node->left == old(node->left);
}

contract void Copy(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    views new->left;
    ensures new->left == old(new->left);
}

contract void Rotate(struct node* old, struct node* new) {
    requires new != 0;
    views new->left;
    views new->right;
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
    views parent->left;
    views parent->right;
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
