# A borrowing composite survives a call that owns it

`box(p)` owns the struct's fields and views the array its `d` field points
at: a struct holding a borrow. `setup` builds one from a viewed input, so
the produced composite keeps that input's loan open (step 7 of fix-views);
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
    consumes object(p);
    views src(d, n);
    produces box(p);
    ensures p->b == n;
    ensures p->d == d;
} by {
    execute();
    fold(box(p));
    simp();
}

int32 bump(struct s* p) {
    requires 0 < p->b;
    owns box(p);
    ensures p->b == old(p->b);
    ensures p->d == old(p->d);
} by {
    unfold(box(p));
    execute();
    fold(box(p));
    simp();
}

int32 probe(struct s* p, int32 d[], int32 n) {
    requires 0 < n;
    consumes object(p);
    views src(d, n);
    produces box(p);
    ensures result == n;
} by {
    step();
    step();
    step();
    transport(at(statement(2).entry, p->b) == n, p->b == n) using {
        at(statement(2).entry, p->b) == n;
    }
    step();
    step();
    simp();
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
