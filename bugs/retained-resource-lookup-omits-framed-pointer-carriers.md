# Retained resource lookup omits checked framed pointer carriers

Soundness: incomplete. The archived object-model implementation rejects a
supported C loop proof when the surface rewrite and retained kernel checker
use different candidate-discovery paths. No false acceptance is demonstrated.

Priority: P2. Branch regression blocking the affected activation.

## Reproduction and evidence

The following complete reduction passes fresh, expanded-source and retained
checking on the entry-fold repair delivered in PR #937. After the loop escape
repair at `6b8c5a1bb`, the archive rejects its `unfold` with
`the rewritten composite is absent from both resource representations`.

# A loop resource can select its backing through a framed descriptor field
```c filename=probe.c
struct holder { int32* data; };
void probe(struct holder* h, int32 n) {
    int32 i = 0;
    while (i < n) { h->data[i] = 1; i++; }
}
```
```click
verifying "probe.c";
resource cells(data: int32*, n: int32) { owns data[0..n]; }
void probe(struct holder* h, int32 n) {
    requires 0 <= n;
    requires n <= 536870911;
    views h->data;
    owns cells(h->data, n);
} by {
    step(); step();
    loop {
        owns cells(h->data, n);
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        initialize by simp;
        preserve by {
            unfold(cells(h->data, n));
            step(); step();
            fold(cells(h->data, n));
            close_invariants();
        }
    }
    execute(); simp();
}
```
```expect
pass
```

A bounded local probe compares the two existing lookup paths. The broad
same-family check reports both arguments equal (`[true, true]`); the narrowed
pointer-root index reports zero candidates. The surface's incremental consumption
uses the broader family index and consumes the actual held head. The retained
kernel check cannot rediscover that head through its pointer-root index.

The selected complete-cell frame relation already canonicalizes the two pointer
carriers to the same immutable read. Candidate discovery must cover that relation
without scanning unrelated resource holdings. A candidate index is not proof:
argument equality, pointer origin and ownership quantity still need their existing
checks. Numeric address equality must not create a typed-place witness.

Correcting discovery exposes a second disagreement: the surface unfolds the
written selector again while the retained kernel expands the selected resource's
stored arguments. They produce equivalent but differently spelled memory facts,
and the kernel rejects an unchecked pure-fact delta. Expand the selected C-value
arguments consistently in both paths; retain existing handling of non-C indices.

## Acceptance

- Verify the reduction fresh, expand and verify its rewritten proof, and recheck
  a retained session; do not change its C or claims.
- Keep candidate lookup bounded by selected read/frame evidence and indexed
  related holdings. Include deterministic multi-size coverage beside unrelated
  loaded-pointer resources and a withdrawal control for index maintenance.
- Reject changed or partially written pointer cells, including under asserted
  numeric address equality, and retain strict-native/explicit-validity controls.
- Recheck the original normal example stage. Report later failures separately
  from the reduced rewrite repair; retain all existing work budgets.

## Preserved recovery candidate

The recovery tree now indexes producer read identities as well as pointer roots,
including unconditional checked frame canonicalization at publication. Queries
also use their own checked frame evidence, then run the unchanged argument and
quantity checks. Removing a resource removes its read-index entries. The surface
uses the selected C-value arguments when expanding an unfold; non-C indices keep
their existing handling.

All 31 selected pointer-designation, native-span and loop-carrier kernel tests
pass. The new regression bounds query work below 100 units beside 16, 64, 256
and 1,024 unrelated loaded-pointer resources, checks withdrawal, and rejects
partial writes even under numeric address equality. Both C++ member-domain
rejection fixtures pass. Eight of nine selected resource-unfold Markdown fixtures
pass; the ninth (`resource_unfold_names_unmatched_body_cells`) fails with the
same pointer-arithmetic error on the earlier `6b8c5a1bb` checkpoint. The archived
fieldless entry-fold fixture also retains its preexisting rejection; upstream
PR #937 already repairs that independent bug.

The full normal example stage checks the same 52 projects: 39 pass and 13 fail
in 137.45s, with no new failing project relative to `86abef177`. Fork/join passes
all four proof modes; an escape-only `6b8c5a1bb` executable already passes that
original project, so its restoration is credited to the earlier member-escape
repair, not this index candidate.

The original reduction now passes the retained `unfold`, but fails later at its
post-store `fold(cells(h->data, n))`. Arena still exhausts its unchanged control
budget. This is not a green activation or a complete repair of the reduction.

A follow-up safeguard retains each entry's publication-time read-index keys
for withdrawal instead of recomputing them after late producer frame edges.
The multi-size lookup regression and a dedicated late-edge withdrawal test both
pass on this follow-up. The 39/52 example-stage verdict above is for the initial
candidate; no additional full stage is claimed for the withdrawal-only change.
