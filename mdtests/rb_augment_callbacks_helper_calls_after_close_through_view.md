# A viewed suite's callbacks stay callable after the open closes

The same helper as `rb_augment_callbacks_helper_rejects_call_after_close.md`,
with the suite viewed instead of owned. The open closes before the third
call, as there, but the call is still authorized: the caller's stable view of
`callback_suite(augment)` lasts the whole function, its one-level projection
backs the callee's read of `augment->rotate`, and the body's `Rotate` fact is
loan-stable because the cell it describes cannot change under the view. The
open exposed nothing the view did not already cover, so its close removes
nothing the call needs. With an owned suite the close folds the cells away
and the same call is refused.

```c filename=rb_augment_callbacks_call_after_close_view.c
struct node {
    struct node *left;
    struct node *right;
};

struct rb_augment_callbacks {
    void (*propagate)(struct node *node, struct node *stop);
    void (*copy)(struct node *old, struct node *new);
    void (*rotate)(struct node *old, struct node *new);
};

void dummy_propagate(struct node *node, struct node *stop) {
    node->left = stop;
}
void dummy_copy(struct node *old, struct node *new) { }
void dummy_rotate(struct node *old, struct node *new) { }

void erase_mutating(struct node *node, struct node *parent,
                    struct rb_augment_callbacks *augment) {
    augment->propagate(parent, 0);
    augment->copy(node, parent);
    augment->rotate(node, parent);
}
```

```click
abstract resource spare(value: int32);

verifying "rb_augment_callbacks_call_after_close_view.c";

contract void Propagate(struct node* node, struct node* stop) {
    requires node != 0;
    owns &node->left;
    ensures node->left == stop;
}

contract void Copy(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    owns &new->left;
    ensures new->left == old(new->left);
}

contract void Rotate(struct node* old, struct node* new) {
    requires new != 0;
    owns &new->left;
    owns &new->right;
    ensures new->left == old(new->left);
    ensures new->right == old(new->right);
}

resource callback_suite(augment: struct rb_augment_callbacks*) {
    owns &augment->propagate;
    owns &augment->copy;
    owns &augment->rotate;
    fact Propagate(augment->propagate);
    fact Copy(augment->copy);
    fact Rotate(augment->rotate);
}

void erase_mutating(struct node* node, struct node* parent,
                    struct rb_augment_callbacks* augment) {
    requires node != 0;
    requires parent != 0;
    requires separate(memory(object(augment)), memory(object(parent)));
    owns &parent->left;
    owns &parent->right;
    views callback_suite(augment);
    consumes spare(7);
    produces spare(7);
    ensures parent->left == 0;
    ensures parent->right == old(parent->right);
} by {
    open(callback_suite(augment)) {
        step();
        step();
    }
    execute();
    simp();
}
```

```expect
pass
```
