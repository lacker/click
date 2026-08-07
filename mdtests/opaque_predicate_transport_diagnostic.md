# Opaque predicate transport recommends unfolding

An opaque predicate hides the memory it observes, so Click cannot frame it
across even a local-only C transition. Smart `transport` should explain the
explicit proof path rather than expose certificate-reconstruction internals.

```c filename=opaque_predicate_transport_diagnostic.c
int32 preserve_sorted(int32 p[3]) {
    int32 local;
    local = 0;
    return local;
}
```

```click
verifying "opaque_predicate_transport_diagnostic.c";

predicate sorted(p: int32[], n: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and i < j and j < n implies p[i] <= p[j]
        }
    }
}

int32 preserve_sorted(int32 p[3]) {
    requires loadable(p[0..3]);
    requires sorted(p, 3);
    ensures sorted(p, 3);
} by {
    step();
    step();
    transport(at(function.entry, sorted(p, 3)), sorted(p, 3));
    execute();
    simp();
}
```

```expect
fail: `transport` cannot frame opaque predicate `sorted` across C execution because its memory footprint is hidden; run `unfold(sorted);` before the execution steps and transport its unfolded definition
```
