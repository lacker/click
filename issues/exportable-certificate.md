# Export a machine-checkable proof artifact

Found by the 2026-09-01 kernel audit at cb034b21.

Trust in a Click verdict ends at this binary's exit status. `ProofCertificate`
serializes surface operations and "carries no semantic authority of its own"
(`docs/internals/proof-objects.md:129-140`); `click audit` and `click expand`
re-run the same binary on the same or rewritten source. There is no artifact
a smaller, independent checker could validate. The audit's binder-capture
regression ([have-binder-capture.md](have-binder-capture.md)) passes
`click audit`, which shows that an independent artifact check is the missing
line of defense, not a nicety.

## Violated invariant

A verified function should come with evidence that a checker other than the
verifier can validate: the kernel derivations and typed execution evidence
the proof object already retains, serialized with enough structure to be
re-checked by a small trusted core.

## Intended regression

`click verify --emit-certificate out.json` on `examples/linked-list` produces
an artifact, and `click check-certificate out.json` (or an external reference
checker) accepts it. Mutating one derivation step in the artifact makes the
checker reject it. The artifact for the have-binder-capture regression is
rejected by the checker even while the current verifier accepts the proof.

## Acceptance criteria

- The proof object's kernel derivations (`PropositionDerivation`, checked
  execution events, branch partitions, loop rules) serialize to a documented
  format keyed by the exact C function and contract.
- A checker that does not contain the proof search or the surface tactics
  validates the artifact against the C source and sidecar.
- `docs/concepts/what-click-proves.md` documents the trust boundary the
  artifact establishes.
- `scripts/check.sh` passes.

Related: [double-execution.md](double-execution.md), whose typed evidence is
the natural content of this artifact.
