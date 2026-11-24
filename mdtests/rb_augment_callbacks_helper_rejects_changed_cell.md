# A changed callback table cell invalidates its old contract fact

Replacing the `copy` cell after the first callback is a permitted table
mutation, but the new pointer cannot use the old `Copy` fact. The replacement
helper's checked postcondition equates the cell with its callback argument;
the call supplies `dummy_rotate`, so the fresh cell value is exact while the
unaffected `rotate` callback remains usable.

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

void replace_copy(struct rb_augment_callbacks *augment,
                  void (*replacement)(struct node *old, struct node *new)) {
    augment->copy = replacement;
}

void erase_changed(struct node *node, struct node *parent,
                   struct rb_augment_callbacks *augment) {
    augment->propagate(parent, 0);
    replace_copy(augment, dummy_rotate);
    augment->rotate(node, parent);
    augment->copy(node, parent);
}
```

```click
import click::separation;

verifying "rb_augment_callbacks_rejects_changed_cell.c";

contract void Propagate(struct node* node, struct node* stop) {
    requires node != 0;
    owns node->left;
    ensures node->left == old(node->left);
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

void replace_copy(struct rb_augment_callbacks* augment,
                  void (*replacement)(struct node* old, struct node* new)) {
    owns augment->copy;
    ensures augment->copy == replacement;
}

void erase_changed(struct node* node, struct node* parent,
                   struct rb_augment_callbacks* augment) {
    consumes callback_suite(augment);
    requires node != 0;
    requires parent != 0;
    requires separate(memory(*augment), memory(*parent));
    owns parent->left;
    owns parent->right;
} by {
    with(callback_suite(augment)) {
        apply(separation::contains_refl(memory(*augment)));
        apply(separation::contains_subrange(augment as (int32*), 0, 6, 0, 2));
        apply(separation::contains_subrange(augment as (int32*), 0, 6, 2, 4));
        apply(separation::contains_subrange(augment as (int32*), 0, 6, 4, 6));
        apply(separation::contains_subrange(parent as (int32*), 0, 4, 0, 2));
        have separate(memory(parent->left), memory(*augment)) by {
            apply(separation::separate_restrict(memory(*parent), memory(*augment), memory(parent->left), memory(*augment)));
        }
        mark before_propagate;
        step();
        have contains(memory(parent->left), statement(0).footprint) by { close(); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(0).footprint, memory(augment->propagate)));
        have augment->propagate == at(before_propagate, augment->propagate) by { preserve(memory(augment->propagate), statement(0)); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(0).footprint, memory(augment->copy)));
        have augment->copy == at(before_propagate, augment->copy) by { preserve(memory(augment->copy), statement(0)); }
        apply(separation::separate_restrict(memory(parent->left), memory(*augment), statement(0).footprint, memory(augment->rotate)));
        have augment->rotate == at(before_propagate, augment->rotate) by { preserve(memory(augment->rotate), statement(0)); }
    }
    step();
    step();
    step();
}
```

```expect
fail: no contract fact for the function pointer `augment->copy`
```
