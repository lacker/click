# a composite cannot be held at a range whose extent wraps

A composite's contained ranges are stated ranges, so their byte-count guards
are available while the body's own `fact` clauses are evaluated. That is only
sound because the composite cannot be held at a range whose extent wraps in the
first place: the body's clauses are lowered against the instantiated
arguments, and a decidably invalid extent leaves no lowering path.

So there is no route where a wrapped range is folded into a composite, carried
past the fold as ownership, and then unfolded into a body evaluation that reads
it at element granularity. Folding one is refused for the same reason: a fold
has to establish the body's facts in the prover's own context, which the
assumed guards of the body's contained ranges are deliberately not part of.

```c filename=wrapped_slice.c
int32 wrapped_slice(int32* p, int32 n) {
    return p[0];
}
```

```click
resource slice_of(p: int32*, n: int32) {
    views p[0..n];
    fact loadable(p[0..n]);
}

verifying "wrapped_slice.c";

int32 wrapped_slice(int32* p, int32 n) {
    consumes slice_of(p, n);
    requires n == 1073741824;
    requires 0 < n;
    ensures result == p[0] by {
        observe(slice_of(p, n));
        execute();
        simp();
    }
}
```

```expect
fail: the kernel lowering produced 0 paths, not one
```
