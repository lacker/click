# A borrowing composite survives a call that owns it

`box(p)` owns the struct's fields and views the array its `d` field points
at: a struct holding a borrow. `setup` builds one from a viewed input, so
the produced composite keeps that input's borrow open (step 7 of fix-views);
`bump` then takes the whole composite by ownership and returns it, and the
caller still knows `p->b` afterwards through the callee's `old()` ensures.
The same shape verifies under both view semantics.

```click
resource src(d: int32*, n: int32) {
    views d[0..n];
    fact 0 <= n;
}

resource box(p: struct s*) {
    owns p->a;
    owns p->b;
    owns p->d;
    views src(p->d, p->b);
    fact 0 <= p->b;
}

verifying "probe.c";

int32 setup(struct s* p, int32 d[], int32 n) {
    requires 0 <= n;
    consumes *p;
    views src(d, n) as input;
    produces box(p) from input;
    ensures p->b == n;
    ensures p->d == d;
} by {
    observe(src(d, n));
    have separate(memory(*p), memory(d[0..n])) by { close(); }
    have contains(memory(d[0..n]), memory(d[0..n])) by { apply(click::separation::contains_refl(memory(d[0..n]))); }
    have contains(memory(*p), memory(p->a)) by { normalize(); }
    have contains(memory(*p), memory(p->b)) by { normalize(); }
    have contains(memory(*p), memory(p->d)) by { normalize(); }
    have separate(memory(p->a), memory(d[0..n])) by {
        apply(click::separation::separate_restrict(memory(*p), memory(d[0..n]), memory(p->a), memory(d[0..n])));
    }
    have separate(memory(p->b), memory(d[0..n])) by {
        apply(click::separation::separate_restrict(memory(*p), memory(d[0..n]), memory(p->b), memory(d[0..n])));
    }
    have separate(memory(p->d), memory(d[0..n])) by {
        apply(click::separation::separate_restrict(memory(*p), memory(d[0..n]), memory(p->d), memory(d[0..n])));
    }
    step_until(function.exit);
    fold(box(p));
    close();
}

int32 bump(struct s* p) {
    requires 0 < p->b;
    owns box(p);
    ensures p->b == old(p->b);
    ensures p->d == old(p->d);
} by {
    unfold(box(p));
    step_until(function.exit);
    fold(box(p));
    close();
}

int32 probe(struct s* p, int32 d[], int32 n) {
    requires 0 < n;
    consumes *p;
    views src(d, n) as input;
    produces box(p) from input;
    ensures result == n;
} by {
    step();
    step();
    step();
    have p->b == n by { close(); }
    step();
    step();
    step();
    step();
    close();
}
```

```c filename=probe.c
struct s { int32 a; int32 b; int32* d; };

int32 setup(struct s* p, int32 d[], int32 n) { p->a = 0; p->b = n; p->d = d; return 0; }
int32 bump(struct s* p) { p->a = 1; return 0; }
int32 probe(struct s* p, int32 d[], int32 n) { int32 r; r = setup(p, d, n); r = bump(p); r = p->b; return r; }
```

```expect
pass
```
