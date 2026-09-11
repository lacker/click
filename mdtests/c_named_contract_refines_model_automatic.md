# Automatic formation admits a modeled resource guarantee

A named contract with a resource proof parameter promises that the callback
preserves the instance model. The implementation declares one binder of the
same resource family with the same arguments, so the binding between the two
interfaces is forced and the fact forms at the call site with no theorem.

```c filename=model_cell.c
void preserve(int32* p) { }

int32 accept(void (*step)(int32*)) { return 0; }

int32 caller() { return accept(&preserve); }
```

```click
verifying "model_cell.c";

spec enum Mark { Clear, Set }

resource cell_at(p: int32*) {
    field model: Mark;
    owns p[0..1];
}

contract Preserve(root: cell_at(p)) for void(int32* p) {
    owns root;
    ensures root.model == old(root.model);
}

void preserve(int32* p) {
    owns t: cell_at(p);
    ensures t.model == old(t.model);
} by {
    execute();
    simp();
}

int32 accept(void (*step)(int32*)) {
    requires Preserve(step);
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
pass
```
