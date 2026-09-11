# The refused formation's printed theorem parses and verifies

`c_named_contract_refusal_prints_theorem.md` refuses to form
`AugmentRotate(&bump)` automatically and prints an `executes` theorem. This is
a project of the same shape, so it prints the same skeleton: `bump` guarantees
what `AugmentRotate` needs but does not state it in the same words, and
automatic formation is exact. The skeleton below is pasted in verbatim and
applied at the call site, so the affordance the diagnostic offers is the
affordance the language accepts. Drop the `apply` and the call to `accept`
fails with that diagnostic instead.

```c filename=refusal_roundtrip.c
void bump(int32* p) { }

int32 accept(void (*step)(int32*)) { return 0; }

int32 caller() { return accept(&bump); }
```

```click
verifying "refusal_roundtrip.c";

spec enum Mark { Clear, Set }

resource tree_at(p: int32*) {
    field model: Mark;
    field tag: Mark;
    field revision: int32;
    owns p[0..1];
}

contract AugmentRotate(t: tree_at(p)) for void(int32* p) {
    owns t;
    ensures t.revision == 0 implies t.model == old(t.model);
}

void bump(int32* p) {
    owns tree: tree_at(p);
    ensures tree.model == old(tree.model);
} by {
    execute();
    simp();
}

theorem bump_is_augment_rotate() executes bump(int32* p) {
    ensures AugmentRotate(&bump) as { t: r } by {
        step(bump(p), { tree: r });
        simp();
    }
}

int32 accept(void (*step)(int32*)) {
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
