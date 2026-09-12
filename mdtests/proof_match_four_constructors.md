# A four-constructor execution `match`

Nothing about the constructor family's width is special-cased. Four arms cost
four entries and three frontier splits, each arm proving its own result model
and its own return value.

```c filename=read.c
int read(int* p) { return *p; }
```

```click
verifying "read.c";

spec enum Quad { Zero, One, Two, Other(int) }

function quad_code(q: Quad) -> int {
    match q {
        Quad::Zero => 0,
        Quad::One => 1,
        Quad::Two => 2,
        Quad::Other(value) => value,
    }
}

resource cell(p: int*) {
    field model: Quad;
    match model {
        Quad::Zero => { owns p[0..1]; fact p[0] == 0; },
        Quad::One => { owns p[0..1]; fact p[0] == 1; },
        Quad::Two => { owns p[0..1]; fact p[0] == 2; },
        Quad::Other(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

int read(int* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
    ensures result == quad_code(old(c.model));
} by {
    match c.model {
        Quad::Zero => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Quad::Zero }, {});
            have quad_code(old(c.model)) == 0 by {
                rewrite(old(c.model) == Quad::Zero);
                unfold(quad_code(Quad::Zero));
                normalize();
            }
            simp();
        },
        Quad::One => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Quad::One }, {});
            have quad_code(old(c.model)) == 1 by {
                rewrite(old(c.model) == Quad::One);
                unfold(quad_code(Quad::One));
                normalize();
            }
            simp();
        },
        Quad::Two => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Quad::Two }, {});
            have quad_code(old(c.model)) == 2 by {
                rewrite(old(c.model) == Quad::Two);
                unfold(quad_code(Quad::Two));
                normalize();
            }
            simp();
        },
        Quad::Other(value) => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Quad::Other(value) }, {});
            have quad_code(old(c.model)) == value by {
                rewrite(old(c.model) == Quad::Other(value));
                unfold(quad_code(Quad::Other(value)));
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
