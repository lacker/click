# Current fact bodies cannot fold through an unbound view

A fact that reads current memory may be admitted by the resource definition,
but folding it requires the exact live stable-view dependency that supplied the
read.  An ordinary unbound view must fail closed.

```c filename=resource_view_fact_unbound_fold_rejected.c
int32 make_readback(int32 p[]) {
    return p[0];
}
```

```click
resource readback(p: int32*) {
    views p[0..1];
    fact p[0] == 0;
}

verifying "resource_view_fact_unbound_fold_rejected.c";

int32 make_readback(int32 p[]) {
    consumes p[0..1];
    produces readback(p);
} by {
    execute();
    fold(readback(p));
}
```

```expect
fail: missing pure fact
```
