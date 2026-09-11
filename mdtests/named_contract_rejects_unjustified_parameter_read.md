# A named contract cannot address a segment through a cell it does not hold

`views old->left->augmented` reads the parameter cell `old->left` to name
its segment. The contract below drops the `views old->left` clause that
holds that cell, so nothing in its own clause set justifies the read: the
contract is addressing memory through a link it has no access to. Preparing
the contract refuses it, with the same missing fact a `requires old->left !=
0` reading the same cell reports.

```c filename=augment_rotate.c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

void bump(struct node *old, struct node *new) { new->augmented = old->left->augmented; }
```

```click
verifying "augment_rotate.c";

contract void AugmentRotate(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires old->left != 0;
    views old->left->augmented;
    owns old->augmented;
    owns new->augmented;
}
```

```expect
fail: missing pure fact: loadable(base=old, bytes=8)
```
