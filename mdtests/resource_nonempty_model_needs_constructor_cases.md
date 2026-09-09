# Nonempty is not yet enough to expose constructor fields

This records a missing proof operation, not an invalid C program or contract.
For an owned `Some(value)` cell the read is safe, and its model is preserved.
The precondition excludes `None` but does not give the proof a name for
`value`. Pure `match` expressions are symbolic; they do not introduce
constructor cases and fresh field bindings into an execution proof.

When proof-level constructor elimination is supported, replace this rejection
with a proof that explicitly names the `Some` field and checks the exhaustive
cases. Do not specialize the precondition to `Some(7)` or alter the C.

```c filename=read.c
int read(int* p) { return *p; }
```

```click
verifying "read.c";

spec enum Maybe { None, Some(int) }
resource cell(p: int*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

int read(int* p) {
    owns c: cell(p);
    requires c.model != Maybe::None;
    ensures c.model == old(c.model);
} by {
    unfold(c);
    execute();
    fold(c);
    simp();
}
```

```expect
fail: resource match requires constructor evidence for the instance field
```
