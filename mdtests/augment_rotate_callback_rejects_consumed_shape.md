# A rotation callback may not consume a resource the named contract lends

`steal` reads only the old augmentation cell, but its contract consumes
`shape(old)`. `AugmentRotate` hands the callback a view of the rebuilt shape and
ownership of two cells; it never transfers a subtree away. A concrete contract
that takes ownership the named contract does not supply cannot satisfy it, so
`AugmentRotate(&steal)` never forms.

```c filename=augment_rotate.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

struct node *rotate_left(struct node *node,
                         void (*augment_rotate)(struct node *old, struct node *new)) {
    struct node *pivot = node->right;
    struct node *middle = pivot->left;
    node->right = middle;
    pivot->left = node;
    augment_rotate(node, pivot);
    return pivot;
}

void bump(struct node *old, struct node *new) { new->augmented = old->augmented + 1; }
void reset(struct node *old, struct node *new) { old->augmented = 0; new->augmented = 0; }
void clobber(struct node *old, struct node *new) { new->augmented = 0; old->left = 0; }
void steal(struct node *old, struct node *new) { new->augmented = old->augmented; }

struct node *rotate_steal(struct node *node) {
    return rotate_left(node, &steal);
}
```

```click
resource shape(node: struct node*) {
    if node != 0 {
        owns node->left;
        owns node->right;
        owns shape(node->left);
        owns shape(node->right);
    }
}

verifying "augment_rotate.c";

contract void AugmentRotate(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= old->augmented;
    requires old->augmented < 1000;
    views shape(new);
    owns old->augmented;
    owns new->augmented;
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
}

void steal(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= old->augmented;
    requires old->augmented < 1000;
    consumes shape(old);
    views shape(new);
    owns old->augmented;
    owns new->augmented;
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
}

struct node* rotate_left(
    struct node* node,
    void (*augment_rotate)(struct node*, struct node*)
) {
    requires AugmentRotate(augment_rotate);
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes node->left;
    consumes node->right;
    consumes shape(node->left);
    consumes shape(node->right);
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    unfold(shape(node->right));
    // Carry the untouched link reads across each store before folding.
    step_until(statement(2).entry);
    have defined(node->left) by { normalize(); }
    have separate(memory(node->left), memory(node->right)) by { close(); }
    have defined(pivot->right) by { normalize(); }
    have separate(memory(pivot->right), memory(node->right)) by { close(); }
    mark before_right;
    step_until(statement(3).entry);
    have separate(statement(2).footprint, memory(node->left)) by {
        normalize() using { at(before_right, separate(memory(node->left), memory(node->right))); };
    }
    have defined(node->left) by { preserve(memory(node->left), statement(2)); }
    have separate(statement(2).footprint, memory(pivot->right)) by {
        normalize() using { at(before_right, separate(memory(pivot->right), memory(node->right))); };
    }
    have defined(pivot->right) by { preserve(memory(pivot->right), statement(2)); }

    have separate(memory(node->left), memory(pivot->left)) by { close(); }
    have defined(node->right) by { normalize(); }
    have node->right == middle by { normalize(); }
    have separate(memory(node->right), memory(pivot->left)) by { close(); }
    have defined(pivot->right) by { normalize(); }
    have separate(memory(pivot->right), memory(pivot->left)) by { close(); }
    mark before_left;
    step_until(statement(4).entry);
    have separate(statement(3).footprint, memory(node->left)) by {
        normalize() using { at(before_left, separate(memory(node->left), memory(pivot->left))); };
    }
    have defined(node->left) by { preserve(memory(node->left), statement(3)); }
    have separate(statement(3).footprint, memory(node->right)) by {
        normalize() using { at(before_left, separate(memory(node->right), memory(pivot->left))); };
    }
    have defined(node->right) by { preserve(memory(node->right), statement(3)); }
    have node->right == at(before_left, node->right) by { preserve(memory(node->right), statement(3)); }
    have node->right == middle by {
        rewrite(node->right, at(before_left, node->right));
        close();
    }
    have pivot->left == node by { normalize(); }
    have separate(statement(3).footprint, memory(pivot->right)) by {
        normalize() using { at(before_left, separate(memory(pivot->right), memory(pivot->left))); };
    }
    have defined(pivot->right) by { preserve(memory(pivot->right), statement(3)); }
    have defined(pivot->left) by { normalize(); }
    fold(shape(node));
    fold(shape(pivot));
    step();
    step();
    close();
}

struct node* rotate_steal(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    requires node != node->right;
    requires 0 <= node->augmented;
    requires node->augmented < 1000;
    consumes node->left;
    consumes node->right;
    consumes shape(node->left);
    consumes shape(node->right);
    owns node->augmented;
    owns node->right->augmented;
    produces shape(result);

    ensures result == old(node->right);
    ensures 0 <= result->augmented;
    ensures result->augmented <= 1000;
} by {
    have AugmentRotate(&steal) by { close(); }
    step_until(function.exit);
}
```

```expect
fail: could not establish `AugmentRotate(&steal)`
```
