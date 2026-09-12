# A declaration list repeats its pointer star per declarator

C writes each declarator's pointer `*` with the declarator, not with the type
specifier, so `struct rb_node *parent = rb_red_parent(node), *gparent, *tmp;` —
the first line of Linux's `__rb_insert` — has three declarators each carrying
its own star. The parser consumed the stars as part of the type and then
demanded a name, so the verbatim line failed with `expected local name, got
'*'` and the whole insert path was unreachable before any proof could start.

The rule is deliberately narrow. A later declarator may repeat exactly the
pointer depth the type specifier already wrote, which gives every declarator
the type the first one has; any other depth is refused by name rather than
typed from the first declarator's. So `int32 *a, *b;` declares two pointers,
while `int32 *a, b;` and `int32 *a, **b;` are refused and are written as
separate declarations.

```c filename=declarator_stars.c
int32 sum_through_pointers(int32 *p, int32 *q) {
    int32 *a = p, *b, *c;

    b = q;
    c = p;
    return a[0] + b[0] + c[0];
}

int32 two_levels(int32 **pp, int32 **qq) {
    int32 **x = pp, **y;

    y = qq;
    return x[0][0] + y[0][0];
}
```

```click
verifying "declarator_stars.c";

int32 sum_through_pointers(int32* p, int32* q) {
    views p[0..1];
    views q[0..1];
    requires p[0] == 1;
    requires q[0] == 2;
    ensures result == 4;
} by {
    execute();
    simp();
}

int32 two_levels(int32** pp, int32** qq) {
    views pp[0..1];
    views qq[0..1];
    views pp[0][0..1];
    views qq[0][0..1];
    requires pp[0][0] == 3;
    requires qq[0][0] == 4;
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
