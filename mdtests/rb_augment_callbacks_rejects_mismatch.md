# A table field bound to the wrong callback is refused

`dummy_copy` satisfies `Copy`: it views the left link of its second argument
and gives it back unchanged. `Rotate` asks for both links of that argument, so
`dummy_copy` does not satisfy it. Binding it to `.rotate` in the table is
therefore a proof failure at the caller, where `&dummy_callbacks` has to
discharge `Rotate(augment->rotate)` from the address the initializer named.
The proof supplies the contract for each callback at its own address so that
the call reaches the mismatched rotation field. Both fields have the same
function signature.

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

resource rb_augment_callbacks_storage(p: struct rb_augment_callbacks*) {
    views p->propagate;
    views p->copy;
    views p->rotate;
}


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
}

void dummy_copy(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    views new->left;
    ensures new->left == old(new->left);
}

void dummy_rotate(struct node* old, struct node* new) {
    requires new != 0;
    views new->left;
    views new->right;
    ensures new->left == old(new->left);
    ensures new->right == old(new->right);
}

void erase_augmented(struct node* node, struct node* parent,
                     const struct rb_augment_callbacks* augment) {
    views rb_augment_callbacks_storage(augment);
    requires Propagate(augment->propagate);
    requires Copy(augment->copy);
    requires Rotate(augment->rotate);
    requires node != 0;
    requires parent != 0;
    views parent->left;
    views parent->right;
    ensures parent->left == old(parent->left);
    ensures parent->right == old(parent->right);
}

void erase_dummy(struct node* node, struct node* parent) {
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    requires node != 0;
    requires parent != 0;
    views parent->left;
    views parent->right;
    ensures parent->left == old(parent->left);
    ensures parent->right == old(parent->right);
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(rb_augment_callbacks_storage(&dummy_callbacks));
    step();
}

theorem dummy_propagate_contract() { ensures Propagate(&dummy_propagate) by { unfold(Propagate(&dummy_propagate)); close(); } }
theorem dummy_copy_contract() { ensures Copy(&dummy_copy) by { unfold(Copy(&dummy_copy)); close(); } }
theorem dummy_rotate_contract() { ensures Rotate(&dummy_rotate) by { unfold(Rotate(&dummy_rotate)); close(); } }
```

```expect
fail: ->rotate)`
```
