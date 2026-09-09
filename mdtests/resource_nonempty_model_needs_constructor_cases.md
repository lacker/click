# Excluding the empty constructor exposes an arbitrary cell payload

The empty constructor closes by an explicitly checked contradiction.
For an owned `Some(value)` cell the read is safe, and its model is preserved.
The precondition excludes `None` but does not give the proof a name for
`value`. Pure `match` expressions are symbolic; they do not introduce
constructor cases and fresh field bindings into an execution proof.

The live arm names the arbitrary `Some` field and preserves ownership.

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
    match c.model {
        Maybe::None => { contradiction(c.model == Maybe::None); },
        Maybe::Some(value) => {
            unfold(c);
            execute();
            fold(c);
            simp();
        },
    }
}
```

```expect
pass
```
