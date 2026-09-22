# A callback fact does not outlive the open that exposed it

The callback suite is opened once; the first callback stores through its owned
node link and the second is still authorized inside the open. The open then
closes before the third call. The cells the body exposed, `augment->rotate`
among them, went back into the folded suite with the close, together with the
body's callback facts, so the call after the close cannot read the callback
pointer it would apply and is refused for the missing view. The permitted
mutation inside the open does not change that: the scope, not the mutation,
bounds what the body exposes.

```c filename=rb_augment_callbacks_call_after_close.c
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

verifying "rb_augment_callbacks_call_after_close.c";

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
    owns callback_suite(augment);
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
fail: missing resource fact
```
