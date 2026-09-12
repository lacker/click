# Consuming a callback suite retires its callback facts

The suite is consumed by a checked helper between the first and later
callback calls. The old `Copy` fact is therefore unavailable afterward.

```c filename=rb_augment_callbacks_consumes_suite.c
struct node { struct node *left; struct node *right; };
struct rb_augment_callbacks {
    void (*propagate)(struct node *node, struct node *stop);
    void (*copy)(struct node *old, struct node *new);
    void (*rotate)(struct node *old, struct node *new);
};
void dummy_propagate(struct node *node, struct node *stop) { }
void dummy_copy(struct node *old, struct node *new) { }
void dummy_rotate(struct node *old, struct node *new) { }
void discard_suite(struct rb_augment_callbacks *augment) { }
void erase_discarded(struct node *node, struct node *parent,
                     struct rb_augment_callbacks *augment) {
    augment->propagate(parent, 0);
    discard_suite(augment);
    augment->copy(node, parent);
    augment->rotate(node, parent);
}
```

```click
verifying "rb_augment_callbacks_consumes_suite.c";

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

void discard_suite(struct rb_augment_callbacks* augment) {
    consumes callback_suite(augment);
} by auto;

void erase_discarded(struct node* node, struct node* parent,
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
