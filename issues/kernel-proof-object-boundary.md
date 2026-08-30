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
and loop/region flags. Kernel `ProofExecutionState` pairs that core with an
opaque `ExecutionProofPresentation` containing only snapshot selectors, source
spellings, deferred Surface tactics, construction cursors, and provenance; the
presentation does not duplicate semantic execution state. Snapshot-blind and
alpha-equivalence fact-index
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
are kernel state operations. The opaque kernel `ProofObject` handle now owns
the shared semantic state and its focused branch cursor; the language `Proof`
wrapper retains only checking context and Surface certificate lineage. Kernel
`ProofExecutionState` now pairs the semantic execution core with an opaque
language presentation, allowing `ProofObject` alone to construct a typed
function-exit finalization view. It also owns the completion witness required
by terminal certificate extraction. The same core-plus-opaque-presentation
shape now applies to result-aware function outcomes: the kernel owns the
result, state, execution facts, requirements, and crossed effects used by
outcome rules. The language attachment retains only Surface proposition
records, selectors, and diagnostic provenance. Primitive proposition-closing
rules (`assumption`, `normalize`, `split`, disjunction selection, and finite
enumeration) are named `ProofObject` operations. They check the focused
obligation and return an opaque kernel successor directly; the language
dispatcher only selects the operation, translates its typed failure into the
existing diagnostic, and records Surface provenance. Higher-level checked
operations still need the same kernel-owned API treatment.

Language-only proof environments now live in
`src/lang/click/proof/language_context.rs`, and Surface certificate lineage and
checkpoints live in `proof_object/provenance.rs`. They wrap and describe the
opaque checked handle without becoming semantic state.

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
