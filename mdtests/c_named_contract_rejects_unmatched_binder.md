# An implementation binder the contract does not supply is refused

The named contract declares one proof parameter; the implementation needs two
instances. There is no instance for the second binder, so the binding is not
forced in either direction and the fact does not form. The printed theorem
shows why no explicit proof rescues it either: the step map needs an `r2` that
the conclusion's `as` map has no parameter to introduce.

```c filename=unmatched_binder.c
void needs_two(int32* p, int32* q) { }

int32 accept(void (*step)(int32*, int32*)) { return 0; }

int32 caller() { return accept(&needs_two); }
```

```click
verifying "unmatched_binder.c";

spec enum Mark { Clear, Set }

resource cell_at(p: int32*) {
    field model: Mark;
    owns p[0..1];
}

resource other_at(p: int32*) {
    field model: Mark;
    owns p[0..1];
}

contract PreserveOne(root: cell_at(p)) for void(int32* p, int32* q) {
    owns root;
    ensures root.model == old(root.model);
}

void needs_two(int32* p, int32* q) {
    owns t: cell_at(p);
    owns u: other_at(q);
    ensures t.model == old(t.model);
    ensures u.model == old(u.model);
} by {
    execute();
    simp();
}

int32 accept(void (*step)(int32*, int32*)) {
    requires PreserveOne(step);
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
fail: function `needs_two` does not satisfy named contract `PreserveOne` automatically;
prove it explicitly:
theorem needs_two_is_preserve_one() executes needs_two(int32* p, int32* q) {
    ensures PreserveOne(&needs_two) as { root: r1 } by {
        step(needs_two(p, q), { t: r1, u: r2 });
        simp();
    }
}
```
