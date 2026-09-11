# A table field bound to the wrong callback is refused

`dummy_copy` satisfies `Copy`: it views the left link of its second argument
and gives it back unchanged. `Rotate` asks for both links of that argument, so
`dummy_copy` does not satisfy it. Binding it to `.rotate` in the table is
therefore a proof failure at the caller, where `&dummy_callbacks` has to
discharge `Rotate(augment->rotate)` by concrete formation from the address the
initializer named. Nothing about the signature distinguishes the two fields;
only the contracts do.

```c filename=rb_augment_callbacks_mismatch.c
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
    .rotate = dummy_copy
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
verifying "rb_augment_callbacks_mismatch.c";

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
fail: function `dummy_copy` does not satisfy named contract `Rotate`
```
