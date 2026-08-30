# Put the checked proof object inside the kernel boundary

The persistent `Proof` object owns soundness-critical state and transitions,
but most of its implementation currently lives under `src/lang/click/proof/`
beside smart search, Surface Click lowering, diagnostics, and certificate
serialization. A bug in proof construction, `apply_step`, branch or scope
joins, or completion can accept an invalid proof, while a bug in smart search
must only reject a proof or choose an unhelpful checked path. The code layout
does not make that trust distinction clear.

The first extraction moved branch and split identities plus persistent branch
topology to `src/kernel/proof/branches.rs`. Smart search now lives outside
`proof_object/` and consumes an immutable internal planning interface instead
of the proof's private state, provenance node, focus, or constructors. The
contextual Surface Click lowering has also moved out of `proof_object/`; the
checked core retains only its derivation lineage and certificate attribution.
The proof-specific persistent storage containers now live in
`src/kernel/proof/storage.rs`; they carry no surface syntax or transition
authority. Typed execution frontiers and loop-effect obligations now live in
`src/kernel/proof/execution.rs`. That module also owns `ExecutionProofCore`:
the path's C state, checked execution facts and loop rules, semantic freshness,
and loop/region flags. The language-layer `ExecutionProofState` is an explicit
wrapper containing only snapshot selectors, source spellings, deferred Surface
tactics, construction cursors, and provenance; it does not duplicate semantic
execution state. Snapshot-blind and alpha-equivalence fact-index
keys live in `src/kernel/proof/fact_keys.rs`, and surface-independent fact
matching, transport, conflict, and equivalence rules live in
`src/kernel/proof/fact_reasoning.rs`. Surface fact-selection policy,
diagnostics, and budgeted smart premise search remain in the language layer.
The persistent `ProofFacts` store and its semantic indexes now live in
`src/kernel/proof/facts.rs`; language code can only use its named queries and
persistent successor operations. Kernel `ProofState`, `ProofBranch`, and
`ProofBranchState` now own the immutable state and open-branch representation,
with language records carried only as opaque parameters. The complete
proposition/frontier/outcome obligation enum, effect selections, result-aware
outcome state, and checked frame authority live in
`src/kernel/proof/obligations.rs`. Goal-preserving fact/execution successors,
strict frontier successors, obligation replacement, and conditional discharge
are kernel state operations. The remaining `Proof` handle, higher-level
checked operations, and finalization still need a kernel-owned API.

Language-only proof environments now live in
`src/lang/click/proof/language_context.rs`, and Surface certificate lineage and
checkpoints live in `proof_object/provenance.rs`. This leaves the persistent
checked state visibly separate from both dependencies before its final move.

## Intended regression

Keep a focused module-boundary test or compile-time visibility check showing
that code in the smart-planning layer can inspect a proof and request named
checked operations, but cannot construct a proof state, branch identity,
derivation node, semantic successor, or completed goal directly. Existing
proof-object branch, scope, transaction, certificate, and deterministic-scaling
tests must continue to pass without changing Surface Click or C fixtures.

## Acceptance criteria

- The opaque persistent `Proof` representation, branch and split topology,
  checked logical/execution/resource transitions, structural split/scope/join
  operations, and completion/finalization authority live under `src/kernel/`.
- `src/lang/click/proof/` retains Surface `ProofStep` lowering, checked-driver
  orchestration, smart planning, diagnostics, and certificate extraction or
  rendering.
- Smart tactics receive only read-only proof queries and named checked
  operations. They cannot mutate semantic state or manufacture a successor.
- `ProofStep` and `ProofCertificate` remain Surface Click provenance and
  serialization, not kernel evidence or a second ordinary checking engine.
- Technical code and architecture documentation call the soundness-critical
  component the **kernel**, without introducing an alternate component name.
- Verification behavior, diagnostics, expansion output, and the deterministic
  scaling bounds remain unchanged, and `scripts/check.sh` passes.
