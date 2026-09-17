# Three owned callbacks survive an allowed body mutation

The callback suite is opened once. The first callback stores through its owned
node link, and the two later callback calls remain authorized. An unrelated
framed token also survives the sequence.

```c filename=rb_augment_callbacks_mutates_body.c
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

verifying "rb_augment_callbacks_mutates_body.c";

contract void Propagate(struct node* node, struct node* stop) {
    requires node != 0;
    owns node->left;
    ensures node->left == stop;
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

resource callback_suite(augment: struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact Propagate(augment->propagate);
    fact Copy(augment->copy);
    fact Rotate(augment->rotate);
}

void erase_mutating(struct node* node, struct node* parent,
                    struct rb_augment_callbacks* augment) {
    requires node != 0;
    requires parent != 0;
    requires separate(memory(object(augment)), memory(object(parent)));
    owns parent->left;
    owns parent->right;
    views callback_suite(augment);
    consumes spare(7);
    produces spare(7);
    ensures parent->left == 0;
    ensures parent->right == old(parent->right);
} by {
    open(callback_suite(augment)) {
        execute();
    }
    simp();
}
```

```expect
pass
```
