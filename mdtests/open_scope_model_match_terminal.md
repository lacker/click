# Model-match arms complete execution inside a borrowed resource scope

The two live arms bind different constructor payloads and both return the
owned cell unchanged. The borrowed table must close on both return paths.

```c filename=scope_match.c
int32 read(int32* p) { return *p; }
```

```click
verifying "scope_match.c";
spec enum Pair { First(int32), Second(int32) }
resource cell(p: int32*) {
    field model: Pair;
    match model {
        Pair::First(value) => { owns *p; fact *p == value; },
        Pair::Second(value) => { owns *p; fact *p == value; },
    }
}
resource table(p: int32*) { views *p; fact *p == 7; }
int32 read(int32* p) {
    owns c: cell(p);
    views table(p + 1);
    ensures c.model == old(c.model);
    ensures *(p + 1) == 7;
} by {
    with(table(p + 1)) {
        match c.model {
            Pair::First(value) => {
                unfold(c);
                step_until(function.exit);
                let c = fold(cell(p), { model: Pair::First(value) });
                close();
            },
            Pair::Second(value) => {
                unfold(c);
                step_until(function.exit);
                let c = fold(cell(p), { model: Pair::Second(value) });
                close();
            },
        }
    }
}
```

```expect
pass
```
