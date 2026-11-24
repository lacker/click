# Consuming a callback suite retires its callback facts

The owned suite is opened for the first callback and closed exactly once.
It is then consumed by a checked helper between the first and later callback
calls. The old `Copy` fact is therefore unavailable afterward. The suite also supplied
the cell views, so the next callback first fails to read `augment->copy`.

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
import click::separation;

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
}

void erase_discarded(struct node* node, struct node* parent,
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
}
```

```expect
fail: missing resource fact `views augment->copy`
```
