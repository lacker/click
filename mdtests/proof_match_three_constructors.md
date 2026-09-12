# A three-constructor execution `match`

A proof `match` splits the execution frontier once per constructor, not once
per pair: the arms of a wider `spec enum` are joined by a tree of frontier
splits, so a three-constructor model needs one contracted function, not three.

Each arm here names its own constructor, folds its own result model, and
returns its own value, so the join has to keep three distinct outcomes rather
than force the arms to agree on one state.

```c filename=read.c
int read(int* p) { return *p; }
```

```click
verifying "read.c";

spec enum Tri { Zero, One, Other(int) }

function tri_code(t: Tri) -> int {
    match t {
        Tri::Zero => 0,
        Tri::One => 1,
        Tri::Other(value) => value,
    }
}

resource cell(p: int*) {
    field model: Tri;
    match model {
        Tri::Zero => { owns p[0..1]; fact p[0] == 0; },
        Tri::One => { owns p[0..1]; fact p[0] == 1; },
        Tri::Other(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

int read(int* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
    ensures result == tri_code(old(c.model));
} by {
    match c.model {
        Tri::Zero => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Tri::Zero }, {});
            have tri_code(old(c.model)) == 0 by {
                rewrite(old(c.model) == Tri::Zero);
                unfold(tri_code(Tri::Zero));
                normalize();
            }
            simp();
        },
        Tri::One => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Tri::One }, {});
            have tri_code(old(c.model)) == 1 by {
                rewrite(old(c.model) == Tri::One);
                unfold(tri_code(Tri::One));
                normalize();
            }
            simp();
        },
        Tri::Other(value) => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Tri::Other(value) }, {});
            have tri_code(old(c.model)) == value by {
                rewrite(old(c.model) == Tri::Other(value));
                unfold(tri_code(Tri::Other(value)));
                normalize();
            }
            simp();
        },
    }
}
```

```expect
pass
```
