# The struct-pointer skeleton parses and verifies

`c_named_contract_refusal_prints_struct_theorem.md` prints an `executes`
theorem whose parameter list reads `struct node* p`. This is a project of the
same shape, and the skeleton is pasted in verbatim and applied at the call
site, so the spelling the diagnostic offers is a spelling the language
accepts. Drop the `apply` and the call to `accept` fails with that diagnostic
instead.

```c filename=refusal_struct_roundtrip.c
struct node {
    int32 augmented;
};

void bump(struct node* p) { }

int32 accept(void (*step)(struct node*)) { return 0; }

int32 caller() { return accept(&bump); }
```

```click
verifying "refusal_struct_roundtrip.c";

spec enum Mark { Clear, Set }

resource tree_at(p: struct node*) {
    field model: Mark;
    field tag: Mark;
    field revision: int32;
    owns p->augmented;
}

contract AugmentRotate(t: tree_at(p)) for void(struct node* p) {
    owns t;
    ensures t.revision == 0 implies t.model == old(t.model);
}

void bump(struct node* p) {
    owns tree: tree_at(p);
    ensures tree.model == old(tree.model);
} by {
    execute();
    simp();
}

theorem bump_is_augment_rotate() executes bump(struct node* p) {
    ensures AugmentRotate(&bump) as { t: r } by {
        step(bump(p), { tree: r });
        simp();
    }
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
    apply(bump_is_augment_rotate());
    execute();
    simp();
}
```

```expect
pass
```
