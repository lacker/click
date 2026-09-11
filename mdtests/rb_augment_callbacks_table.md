# A const callback table discharges three named field contracts

`dummy_callbacks` binds the three fields of `struct rb_augment_callbacks` to
the three no-op helpers with bare designators, the way `lib/rbtree.c` writes
`static const struct rb_augment_callbacks dummy_callbacks = { .propagate =
dummy_propagate, ... }`. `erase_dummy` passes `&dummy_callbacks` to the
erase-shaped helper, and each of the helper's three requirements is discharged
by concrete formation from the address the initializer named: `Propagate` from
`&dummy_propagate`, `Copy` from `&dummy_copy` and `Rotate` from
`&dummy_rotate`. The three contracts differ, so a swapped binding is a proof
failure and not a signature coincidence;
`mdtests/rb_augment_callbacks_rejects_mismatch.md` binds `.rotate` to
`dummy_copy` and is refused.

This fixture states the three facts on the helper directly rather than through
the `callback_suite` resource of `mdtests/rb_augment_callbacks_helper.md`. A
resource body can only `owns` the memory it packages, and the memory of a
file-scope `const` table is never owned by anybody, so
`fold(callback_suite(&dummy_callbacks))` asks for
`owns global:dummy_callbacks...` and cannot be discharged here. The abstract
half of the pair carries the resource form.

The callbacks only `views` the links they talk about, which is what the no-op
bodies actually do. An `owns` footprint on more than one of them cannot be
used together with the resource form today: see the note in
`mdtests/rb_augment_callbacks_helper.md`.

```c filename=rb_augment_callbacks_table.c
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
verifying "rb_augment_callbacks_table.c";

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

void dummy_propagate(struct node* node, struct node* stop) {
    requires node != 0;
    views node->left;
    ensures node->left == old(node->left);
} by {
    execute();
    simp();
}

void dummy_copy(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    views new->left;
    ensures new->left == old(new->left);
} by {
    execute();
    simp();
}

void dummy_rotate(struct node* old, struct node* new) {
    requires new != 0;
    views new->left;
    views new->right;
    ensures new->left == old(new->left);
    ensures new->right == old(new->right);
} by {
    execute();
    simp();
}

void erase_augmented(struct node* node, struct node* parent,
                     const struct rb_augment_callbacks* augment) {
    views object(augment);
    requires loadable(augment->propagate);
    requires loadable(augment->copy);
    requires loadable(augment->rotate);
    requires Propagate(augment->propagate);
    requires Copy(augment->copy);
    requires Rotate(augment->rotate);
    requires node != 0;
    requires parent != 0;
    views parent->left;
    views parent->right;
    ensures parent->left == old(parent->left);
    ensures parent->right == old(parent->right);
} by {
    execute();
    simp();
}

void erase_dummy(struct node* node, struct node* parent) {
    requires node != 0;
    requires parent != 0;
    views parent->left;
    views parent->right;
    ensures parent->left == old(parent->left);
    ensures parent->right == old(parent->right);
} by {
    execute();
    simp();
}
```

```expect
pass
```
