# A wide proof `match` still has to cover every constructor

Wider constructor families are supported, but exhaustiveness is not relaxed
with them: a three-constructor model matched with two arms is refused before
any arm runs.

```c filename=read.c
int read(int* p) { return *p; }
```

```click
verifying "read.c";

spec enum Tri { Zero, One(int), Two(int) }

resource cell(p: int*) {
    field model: Tri;
    match model {
        Tri::Zero => { owns p[0..1]; fact p[0] == 0; },
        Tri::One(value) => { owns p[0..1]; fact p[0] == value; },
        Tri::Two(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

int read(int* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
} by {
    match c.model {
        Tri::Zero => { unfold(c); execute(); fold(c); simp(); },
        Tri::One(value) => { unfold(c); execute(); fold(c); simp(); },
    }
}
```

```expect
fail: proof `match` must cover every constructor exactly once
```
