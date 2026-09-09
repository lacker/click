# Explicit constructor cases over an arbitrary resource model

Both constructors are reachable. `None` models a zero-valued cell, while
`Some` carries an arbitrary payload. Each arm must expose its own memory.

```c filename=read.c
int read(int* p) { return *p; }
```

```click
verifying "read.c";
spec enum Maybe { None, Some(int) }
resource cell(p: int*) {
    field model: Maybe;
    match model {
        Maybe::None => { owns p[0..1]; fact p[0] == 0; },
        Maybe::Some(value) => { owns p[0..1]; fact p[0] == value; },
    }
}
int read(int* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
} by {
    match c.model {
        Maybe::None => { unfold(c); execute(); fold(c); simp(); },
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
