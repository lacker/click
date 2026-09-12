# A changed callback table cell invalidates its old contract fact

Replacing the `copy` cell after the first callback is a permitted table
mutation, but the new pointer cannot use the old `Copy` fact.

```c filename=rb_augment_callbacks_rejects_changed_cell.c
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

void replace_copy(struct rb_augment_callbacks *augment) {
    augment->copy = dummy_rotate;
}

void erase_changed(struct node *node, struct node *parent,
                   struct rb_augment_callbacks *augment) {
    augment->propagate(parent, 0);
    replace_copy(augment);
    augment->rotate(node, parent);
    augment->copy(node, parent);
}
```

```click
verifying "rb_augment_callbacks_rejects_changed_cell.c";

contract void Propagate(struct node* node, struct node* stop) {
    requires node != 0;
    owns node->left;
}

contract void Copy(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    owns new->left;
}

contract void Rotate(struct node* old, struct node* new) {
    requires new != 0;
    owns new->left;
    owns new->right;
}

resource callback_suite(augment: struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact Propagate(augment->propagate);
    fact Copy(augment->copy);
    fact Rotate(augment->rotate);
}

void replace_copy(struct rb_augment_callbacks* augment) {
    owns augment->copy;
} by {
    execute();
    simp();
}

void erase_changed(struct node* node, struct node* parent,
                   struct rb_augment_callbacks* augment) {
    views callback_suite(augment);
    requires node != 0;
    requires parent != 0;
    requires separate(memory(object(augment)), memory(object(parent)));
    owns parent->left;
    owns parent->right;
} by {
    open(callback_suite(augment)) {
        execute();
    }
}
```

```expect
fail: missing resource fact
```
