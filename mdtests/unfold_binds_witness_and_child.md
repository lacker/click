# An unfold pattern binds both a witness and a child

The same pattern opens a resource with a named handle or a family call. The
child becomes the output instance and the witness names a checked body fact.

```c filename=unfold_binds_witness_and_child.c
void by_name(int32 *p) {}
void by_call(int32 *p) {}
```

```click
verifying "unfold_binds_witness_and_child.c";

resource cell() {
    field tag: int32;
}

resource envelope(p: int32*) {
    owns child: cell();
    let base: int32* where base == p;
}

void by_name(int32* p) {
    consumes r: envelope(p);
    produces out: cell();
} by {
    let { child: out, base: q } = unfold(r);
    have q == p by close();
}

void by_call(int32* p) {
    consumes envelope(p);
    produces out: cell();
} by {
    let { base: q, child: out } = unfold(envelope(p));
    have q == p by close();
}
```

```expect
pass
```
