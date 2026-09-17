# A const callback table supplies a packaged read-only suite

This uses the unchanged C from `rb_augment_callbacks_table.md`. The package
contains read-only views of the three callback cells, together with their
named contract facts; it does not claim write ownership of const storage.
Explicit refinement theorems establish the concrete callback facts before
folding. The caller and helper use matching field-level separation premises,
so neither needs `object(&dummy_callbacks)`.

This checks the local caller and helper contracts under their stated separation
premises. It is not the complete Linux erase proof or a program-startup proof
that derives those premises for arbitrary external arguments. The callback
bodies remain no-ops; proving mutation-capable callbacks remains separate work.
This fixture passes ordinary verification; its candidate stable-loan failure is
tracked under rbtree C6 and fix-views, as recorded in `issues/global-variables.md`.

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

resource callback_suite(augment: const struct rb_augment_callbacks*) {
    views augment->propagate;
    views augment->copy;
    views augment->rotate;
    fact Propagate(augment->propagate);
    fact Copy(augment->copy);
    fact Rotate(augment->rotate);
}

void erase_augmented(struct node* node, struct node* parent,
                     const struct rb_augment_callbacks* augment) {
    views callback_suite(augment);
    requires node != 0;
    requires parent != 0;
    requires separate(memory(augment->propagate[0..1]), memory(object(parent)));
    requires separate(memory(augment->copy[0..1]), memory(object(parent)));
    requires separate(memory(augment->rotate[0..1]), memory(object(parent)));
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

void erase_dummy(struct node* node, struct node* parent) {
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    requires separate(memory(dummy_callbacks.propagate[0..1]), memory(object(parent)));
    requires separate(memory(dummy_callbacks.copy[0..1]), memory(object(parent)));
    requires separate(memory(dummy_callbacks.rotate[0..1]), memory(object(parent)));
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
    fold(callback_suite(&dummy_callbacks));
    execute();
    simp();
}

theorem dummy_propagate_contract() { ensures Propagate(&dummy_propagate) by { unfold(Propagate); simp(); } }

theorem dummy_copy_contract() { ensures Copy(&dummy_copy) by { unfold(Copy); simp(); } }

theorem dummy_rotate_contract() { ensures Rotate(&dummy_rotate) by { unfold(Rotate); simp(); } }
```

```expect
pass
```
