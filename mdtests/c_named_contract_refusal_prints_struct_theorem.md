# The printed theorem spells a struct pointer by its tag

`c_named_contract_refusal_prints_theorem.md` prints the skeleton for a
callback over `int32*`. The kernel models `struct node*` as the pointer type
it is laid out as and keeps no struct tag, so the same skeleton would offer
`executes bump(int32* p)` for this project, which is not the C that declares
`bump`. The tag comes from the contract's own declaration, which is on the
surface where the diagnostic is rendered.

```c filename=refusal_struct_theorem.c
struct node {
    int32 augmented;
};

void bump(struct node* p) { }

int32 accept(void (*step)(struct node*)) { return 0; }

int32 caller() { return accept(&bump); }
```

```click
verifying "refusal_struct_theorem.c";

spec enum Mark { Clear, Set }

resource tree_at(p: struct node*) {
    field model: Mark;
    field tag: Mark;
    owns p->augmented;
}

contract AugmentRotate(t: tree_at(p)) for void(struct node* p) {
    owns t;
    ensures t.model == old(t.model);
}

void bump(struct node* p) {
    owns tree: tree_at(p);
    ensures tree.tag == old(tree.tag);
} by {
    execute();
    simp();
}

int32 accept(void (*step)(struct node*)) {
    requires AugmentRotate(step);
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: function `bump` does not satisfy named contract `AugmentRotate` automatically;
prove it explicitly:
theorem bump_is_augment_rotate() executes bump(struct node* p) {
    ensures AugmentRotate(&bump) as { t: r } by {
        step(bump(p), { tree: r });
        simp();
    }
}
```
