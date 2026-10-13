# Rewriting an address reaches a int64 index load

`a[p->q->idx]` loads its index through `p->q`. Rewriting by `p->q == r`
must reach that inner load whatever the index's width, so the goal becomes the
stated `a[r->idx] == 5`. The `int32` index always did; a 64-bit index was
scaled into the address by a different offset form that the rewrite skipped,
and `assumption` then saw the unrewritten goal.

```c filename=rewrite_through_a_int64_index_load.c
struct S { int64 idx; };
struct P { struct S *q; };
void f(struct P *p, struct S *r, int32 *a) {
}
```

```click
verifying "rewrite_through_a_int64_index_load.c";
void f(struct P* p, struct S* r, int32* a) {
    views p->q;
    views r->idx;
    views a[0..10];
    requires p->q == r;
    requires 0 <= r->idx;
    requires r->idx < 10;
    requires a[r->idx] == 5;
    ensures 1 == 1;
} by {
    have a[p->q->idx] == 5 by { rewrite(p->q == r); assumption(); }
    execute();
    simp();
}
```

```expect
pass
```
