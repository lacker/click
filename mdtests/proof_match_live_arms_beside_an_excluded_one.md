# Several live arms next to an excluded constructor

One constructor is impossible and the other three are reachable. The excluded
arm contributes its checked contradiction and no C outcome, so the frontier is
split over the live arms only. Running the live arms one after another on the
same frontier instead would reuse an already advanced state, which the kernel
refuses as an invalid match witness scope.

```c filename=read.c
int read(int* p) { return *p; }
```

```click
verifying "read.c";

spec enum Quad { Zero, One(int), Two(int), Three(int) }

resource cell(p: int*) {
    field model: Quad;
    match model {
        Quad::Zero => { fact p == 0; },
        Quad::One(value) => { owns p[0..1]; fact p[0] == value; },
        Quad::Two(value) => { owns p[0..1]; fact p[0] == value; },
        Quad::Three(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

int read(int* p) {
    owns c: cell(p);
    requires c.model != Quad::Zero;
    ensures c.model == old(c.model);
} by {
    match c.model {
        Quad::Zero => { contradiction(c.model == Quad::Zero); },
        Quad::One(value) => { unfold(c); execute(); fold(c); simp(); },
        Quad::Two(value) => { unfold(c); execute(); fold(c); simp(); },
        Quad::Three(value) => { unfold(c); execute(); fold(c); simp(); },
    }
}
```

```expect
pass
```
