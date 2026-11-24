# Refolding reuses the witness selected by unfolding

A write restores the resource's body fact at the current state. The opened
witness still supplies the pointer in that fact, for both an explicit fold
and the closing fold of a scoped opening.

```c filename=refold_witness.c
void explicit_refold(int32 *p) { *p = 7; }
void scoped_refold(int32 *p) { *p = 7; }
```

```click
verifying "refold_witness.c";

resource cell() { field tag: int32; }

resource envelope(p: int32*) {
    owns child: cell();
    owns *p;
    let base: int32* where base == p and *p == 7;
}

resource tagged(p: int32*) {
    field tag: int32;
    owns *p;
    let base: int32* where base == p and *p == 7;
}

void explicit_refold(int32* p) {
    owns r: envelope(p);
} by {
    let { child: c, base: q } = unfold(r);
    have q == p by close();
    step();
    have *p == 7;
    let r = fold(envelope(p), { child: c });
}

void scoped_refold(int32* p) {
    owns r: tagged(p);
} by {
    let { base: q } = unfold(r);
    have q == p by close();
    fold(r);
    with(r) { step(); }
}
```

```expect
pass
```
