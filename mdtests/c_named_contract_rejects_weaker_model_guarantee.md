# A weaker model guarantee does not refine the named contract

The binding is forced: one binder on each side, same resource family, same
arguments. The implementation still promises nothing about `model`, so the
named contract's model guarantee does not follow and the fact does not form.

```c filename=weaker_model.c
void relabel(int32* p) { }

int32 accept(void (*step)(int32*)) { return 0; }

int32 caller() { return accept(&relabel); }
```

```click
verifying "weaker_model.c";

spec enum Mark { Clear, Set }

resource cell_at(p: int32*) {
    field model: Mark;
    field tag: Mark;
    owns p[0..1];
}

contract Preserve(root: cell_at(p)) for void(int32* p) {
    owns root;
    ensures root.model == old(root.model);
}

void relabel(int32* p) {
    owns t: cell_at(p);
    ensures t.tag == old(t.tag);
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
fail: function `relabel` does not satisfy named contract `Preserve`
```
