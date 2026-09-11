# An unforced instance binding is refused, not ranked

Both declarations name two instances of the same resource family, so nothing
in the two interfaces says which of the implementation's binders stands for
which of the contract's proof parameters. Automatic formation refuses rather
than picking one pairing, and points at the theorem that states the pairing
explicitly.

```c filename=ambiguous_binding.c
void preserve_pair(int32* p, int32* q) { }

int32 accept(void (*step)(int32*, int32*)) { return 0; }

int32 caller() { return accept(&preserve_pair); }
```

```click
verifying "ambiguous_binding.c";

spec enum Mark { Clear, Set }

resource cell_at(p: int32*) {
    field model: Mark;
    owns p[0..1];
}

contract PreservePair(first: cell_at(p), second: cell_at(q))
    for void(int32* p, int32* q)
{
    owns first;
    owns second;
    ensures first.model == old(first.model);
    ensures second.model == old(second.model);
}

void preserve_pair(int32* p, int32* q) {
    owns a: cell_at(p);
    owns b: cell_at(q);
    ensures a.model == old(a.model);
    ensures b.model == old(b.model);
} by {
    execute();
    simp();
}

int32 accept(void (*step)(int32*, int32*)) {
    requires PreservePair(step);
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
fail: function `preserve_pair` does not satisfy named contract `PreservePair` automatically;
prove it explicitly:
theorem preserve_pair_is_preserve_pair() executes preserve_pair(int32* p, int32* q) {
    ensures PreservePair(&preserve_pair) as { first: r1, second: r2 } by {
        step(preserve_pair(p, q), { a: r1, b: r2 });
        simp();
    }
}
```
