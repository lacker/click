# A refused formation prints the explicit refinement theorem

Automatic formation is exact and forced by construction. When it refuses, the
diagnostic prints the `executes` theorem that proves the same obligation with
ordinary tactics, with the contract name, the C parameter list, the target's
proof-parameter map, and the implementation's binder map filled in.

```c filename=refusal_theorem.c
void bump(int32* p) { }

int32 accept(void (*step)(int32*)) { return 0; }

int32 caller() { return accept(&bump); }
```

```click
verifying "refusal_theorem.c";

spec enum Mark { Clear, Set }

resource tree_at(p: int32*) {
    field model: Mark;
    field tag: Mark;
    owns p[0..1];
}

contract AugmentRotate(t: tree_at(p)) for void(int32* p) {
    owns t;
    ensures t.model == old(t.model);
}

void bump(int32* p) {
    owns tree: tree_at(p);
    ensures tree.tag == old(tree.tag);
} by {
    execute();
    simp();
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
    execute();
    simp();
}
```

```expect
fail: function `bump` does not satisfy named contract `AugmentRotate` automatically;
prove it explicitly:
theorem bump_is_augment_rotate() executes bump(int32* p) {
    ensures AugmentRotate(&bump) as { t: r } by {
        step(bump(p), { tree: r });
        simp();
    }
}
```
