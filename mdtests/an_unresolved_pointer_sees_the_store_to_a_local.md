# a pointer the verifier cannot resolve still sees the store to a local

`returned_pointer_to_a_caller_local_may_alias_it.md` is the same C with
`ensures result == p` in the contract, so the read there is resolved to `x` and
refused by substitution. This one drops that clause: nothing at all connects
`q` to `x`, the block of the read stays `Symbolic`, and the only thing that can
frame `q[0]` across `x = 1` is a proof that the store's address is not the
read's — which there is none of, because `q` really is `&x`.

The route this pins is the snapshot comparison behind fact transport. Its
cell-by-cell check used to skip every cell in a `local:` block before asking
anything, so two snapshots differing only in `local:x` were declared to agree
about a load through an unresolved pointer. A store to a *global* was never
skipped, which is why the global-aliasing attack was refused while this one was
not; the skip is gone and both are now decided by one rule.

```c filename=an_unresolved_pointer_sees_the_store_to_a_local.c
int32* echo(int32* p) { return p; }

void v4(void) {
    int32 x;
    int32* q;
    x = 5;
    q = echo(&x);
    x = 1;
}
```

```click
verifying "an_unresolved_pointer_sees_the_store_to_a_local.c";

int32* echo(int32* p) {
    views p[0..1];
    requires p[0] == 5;
    ensures viewable(result[0..1]);
    ensures result[0] == 5;
} by { execute(); simp(); }

void v4() {
    ensures 1 == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    have q[0] == 5 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: the store to `x` may have written it, and nothing tells that address apart from this read.
```
