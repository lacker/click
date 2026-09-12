# Two impossible constructors and one live arm

Preconditions rule out two of the three constructors. Each impossible arm
closes with `contradiction`, which names an exact fact and its negation in that
case, so no C outcome is simulated for it. The one surviving arm runs on the
parent frontier without a split at all: a sole live arm is not joined, so it
keeps the outer routing scope.

```c filename=read.c
int read(int* p) { return *p; }
```

```click
verifying "read.c";

spec enum Tri { Zero, One, Two(int) }

resource cell(p: int*) {
    field model: Tri;
    match model {
        Tri::Zero => { fact p == 0; },
        Tri::One => { fact p == 0; },
        Tri::Two(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

int read(int* p) {
    owns c: cell(p);
    requires c.model != Tri::Zero;
    requires c.model != Tri::One;
    ensures c.model == old(c.model);
} by {
    match c.model {
        Tri::Zero => { contradiction(c.model == Tri::Zero); },
        Tri::One => { contradiction(c.model == Tri::One); },
        Tri::Two(value) => {
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
