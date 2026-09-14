# A produced composite body may not overlap an owner the caller already holds

`repackage` produces `zz_box3(p)`, whose body is `owns p[0..1]`. The caller
already owns `p[0..1]` itself, so the produced head would put a second owner
over the same byte. `take_box` then consumes the head while the caller keeps
reading `p[0]` and still discharges its own owner at exit: one owner became
two. Composing a produced composite checks its one-level frontier against the
facts the destination already holds, so the call is refused.

The check is a separation question, not a ban on producing composites:
`composite_resource_clone_separate_target` views one cursor and produces
another over storage the contract requires to be separate, and it still
verifies.

```c filename=produced_composite_body_overlap.c
int32 f(int32* p) {
    int32 v;
    repackage(p);
    take_box(p);
    v = p[0];
    return v;
}
```

```click
verifying "produced_composite_body_overlap.c";

resource zz_box3(p: int32*) {
    owns p[0..1];
}

extern void repackage(int32* p) {
    produces zz_box3(p);
}

extern void take_box(int32* p) {
    consumes zz_box3(p);
}

int32 f(int32* p) {
    owns p[0..1];
}
```

```expect
fail: produced composite `zz_box3(p)` overlaps a resource the caller already holds: its body `owns p[0..1]` overlaps `owns p[0..1]`
```
