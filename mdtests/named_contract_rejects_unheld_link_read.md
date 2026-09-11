# A named contract cannot address a segment through a link it never holds

`views old->left->augmented` reads the parameter cell `old->left` to name its
segment. The contract below holds neither that cell nor a guard naming it, so
nothing in its own clause set justifies the read: it is addressing memory
through a link it has no access to. Preparing the contract refuses it, naming
the clause by its position and spelling the segment the way the contract wrote
it rather than as the pointer load it lowers to.

`mdtests/named_contract_rejects_unjustified_parameter_read.md` is the same
contract with a `requires old->left != 0` added: the requirement reads the
same cell and is refused for the same missing fact, which is the agreement
between requirements and resource clauses this check exists to keep.
`mdtests/augment_rotate_callback_child_read.md` is the accepted form, where
`views old->left` holds the link.

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
    views old->left->augmented;
    owns old->augmented;
    owns new->augmented;
}
```

```expect
fail: could not address resource clause `old->left->augmented` (resource clause 1 of 3): missing pure fact: loadable(base=old, bytes=8)
```
