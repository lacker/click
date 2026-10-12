# Entry argument reads do not return consumed read authority

```c filename=old_pointer.c
struct box { int *child; };
void split(struct box *p, int *q) { p->child = q; }
int *caller(struct box *p, int *q) { split(p, q); return p->child; }
```

```click
verifying "old_pointer.c";
spec enum Model { Empty, }
resource cell(p: int32*) { field model: Model; fact model == Model::Empty; }
resource holder(p: struct box*) {
    field model: Model;
    owns p->child;
    fact model == Model::Empty;
}
void split(struct box* p, int32* q) {
    consumes h: holder(p);
    produces t: cell(old(p->child));
    produces u: cell(p->child);
} by {
    unfold(h);
    let t = fold(cell(p->child), { model: Model::Empty });
    execute();
    let u = fold(cell(p->child), { model: Model::Empty });
    simp();
}
int32* caller(struct box* p, int32* q) {
    consumes h: holder(p);
    produces t: cell(old(p->child));
    produces u: cell(p->child);
} by {
    let { t: t, u: u } = step(split(p, q), { h: h });
    execute(); simp();
}
```

```expect
fail: missing resource fact `views p->child`
```
