# Smart tactics return structured simple proofs

Click's expansion contract says that a successful smart tactic has discovered a
proof which can be expressed as fast simple tactics. The implementation does
not currently represent that result directly.

All source and internal tactics inhabit `ProofTactic`. `ProofTactic::class()`
then classifies each value dynamically through the data-free `SimpleTactic`,
`SmartTacticKind`, and `ControlFlowTactic` enums. A `ProofReplayPlan` wraps a
`Vec<ProofTactic>` and rejects nested smart tactics, but it accepts internal
operations such as `CertifiedStatementReplay`, `ExactPropositionDerivation`,
and `CertifiedFrame` which are classified as simple while deliberately not
being surface-expressible.

Expansion therefore works indirectly:

```text
smart search
    -> ProofReplayPlan containing internal replay operations
    -> replay those operations while mutating SurfaceReplay
    -> validate the recorded Vec<ProofTactic> as a TacticCertificate
    -> replay that surface certificate
```

The recording step must reconstruct a printable proof while the internal plan
is being replayed. Every internal reasoning path must separately remember to
append the exact surface facts and tactics which reproduce its work. This is a
fragile boundary: search can use a checked fact without the surface recorder
retaining its derivation. Pointer-alias, field-effect, and arithmetic
definedness failures have all exposed variants of this shape.

`field-effect-certificate-loses-exact-equality.md` remains the focused current
regression. In that case smart execution uses the definedness of signed
addition to expose a guarded call postcondition, while the recorded
`step() using` proof omits the evidence for that guard. This issue addresses
the architectural reason such omissions are difficult to locate and easy to
repeat; it does not replace the focused fix.

## Desired model

Introduce a real, data-carrying representation for an expanded proof. The
working names are `SimpleProof` and `SimpleProofStep`; final naming can follow
the surrounding source AST once the boundary is established.

```rust
struct SimpleProof {
    nodes: Vec<SimpleProofNode>,
}

enum SimpleProofNode {
    Step(SimpleProofStep),
    Have { claim: /* ... */, proof: SimpleProof },
    Branch { then_proof: SimpleProof, else_proof: SimpleProof },
    Loop { /* structured simple subproofs */ },
}

enum SimpleProofStep {
    Step,
    StepUsing(/* ... */),
    Assumption,
    Normalize,
    Rewrite(/* ... */),
    TransportUsing(/* ... */),
    // Only deterministic, printable simple tactics.
}
```

The exact split between nodes and steps is not important. The type-level
invariants are:

- every leaf selects one deterministic proof rule;
- every required premise or checked derivation is explicit in the leaf;
- every node has an ordinary `.click` surface spelling;
- replay work is proportional to the represented proof;
- no node searches for an alternate proof or consults ambient history as a
  fallback; and
- structured control flow contains `SimpleProof` children, so the invariant
  holds recursively.

Every successful smart tactic must return a `SimpleProof`. Smart search may use
kernel `PropositionDerivation`, statement-transition evidence, and other
checked internal objects while planning, but success is not reported until it
has constructed the corresponding simple proof. Printing that proof must be a
mechanical traversal, not another proof-discovery or provenance-reconstruction
phase.

```text
smart search
    -> SimpleProof
    -> print ordinary simple Click tactics
    -> independently replay them
```

Kernel proof objects remain distinct where they express genuinely different
judgments. `PropositionDerivation` proves a pure proposition, and certified C
execution evidence proves a statement transition. They are inputs to building
a `SimpleProof`; they must not themselves masquerade as printable simple
tactics. Likewise, the general source AST must continue to represent proofs
which contain smart tactics. This issue is about making the result of smart
search explicit, not mechanically renaming every object containing the word
"proof" or "certificate."

## Failure boundaries

The pipeline must distinguish these failures without requiring inspection of
several replay objects:

1. **Smart planning failure:** search did not find a proof. This is ordinary
   bounded heuristic incompleteness when reported promptly and clearly.
2. **Simple-proof construction failure:** search found an internal route but
   cannot provide complete explicit evidence for a `SimpleProof`. A smart
   tactic must not report success in this state.
3. **Surface support failure:** a checked internal rule has no corresponding
   `SimpleProofStep`. This is missing certificate-language functionality and
   should name the precise unsupported rule.
4. **Replay disagreement:** a constructed and printed `SimpleProof` does not
   replay. This is a lowering or checker bug and must identify the failing
   simple-proof path.

Nodes need stable structural paths such as
`statement[1].call-postcondition[0].antecedent` so diagnostics say which
boundary failed and which proof step was involved. An expansion error should
never collapse these cases into a generic certificate failure.

## Components affected

The new representation should absorb or substantially simplify the current
overlap among:

- the data-free `SimpleTactic` classification;
- simple/control portions of `TacticClass` where the distinction can instead
  be enforced by Rust types;
- `ProofReplayPlan` as a container of replay-only `ProofTactic` values;
- `TacticCertificate` as a second validated wrapper over the same enum;
- `SurfaceReplay` as a mutable tactic-recording side channel;
- `SimpleTactic::is_surface_expressible()`; and
- internal-only `ProofTactic` variants which are currently classified as
  simple.

`ProofTactic` may remain as the parsed source representation, and
`SmartTacticKind` may remain useful for profiling and diagnostics. Do not force
source syntax, kernel derivations, and expanded proof steps into one enum merely
to reduce the type count. The goal is one unambiguous type for the output of
smart tactics.

## Migration order

Keep each step green and independently comprehensible:

1. Add `SimpleProof`/`SimpleProofStep` with construction, deterministic replay,
   surface printing, structural paths, and focused round-trip tests for a few
   existing simple tactics.
2. Convert one narrow pure smart tactic, preferably restricted `simp() using`,
   to return `SimpleProof` directly. Preserve its current explicit-certificate
   regressions and verify profile/expand/audit agreement.
3. Move the remaining pure smart tactics and theorem application across the
   boundary. Add a named simple step whenever a selected kernel derivation has
   no surface rule; do not introduce generic replay search.
4. Convert statement stepping and execution. Require call preconditions,
   arithmetic definedness, fact transports, and guarded postcondition
   elimination to appear as explicit proof steps before execution planning can
   succeed.
5. Convert structured `branch` and `loop` expansions so all nested proofs are
   recursively `SimpleProof` values and retain stable node paths.
6. Delete the internal-plan-to-`SurfaceReplay` recording pipeline and remove
   replay-only variants from the surface tactic representation. Collapse the
   obsolete wrappers and runtime classifications only after all callers use
   the typed boundary.

Do not attempt a flag-day rewrite, weaken existing regressions, reshape C, or
retain the old recorder as a fallback. During migration, each smart tactic must
use exactly one expansion path so disagreement cannot be hidden by trying the
legacy mechanism.

## Acceptance criteria

- Every successful smart tactic returns the same structured `SimpleProof`
  type, recursively containing only deterministic, surface-expressible simple
  steps.
- It is impossible to construct a `SimpleProof` containing a smart tactic or
  an internal-only replay operation.
- Printing a `SimpleProof` is structural and performs no proof search,
  provenance recovery, premise minimization, or ambient-context inspection.
- The printed proof independently replays with work proportional to its
  explicit steps.
- Expansion diagnostics separately identify planning failure, incomplete
  simple-proof construction, missing surface support, and replay disagreement,
  with a stable path to the responsible node.
- `click profile`, `click expand`, and `click audit` operate on the same simple
  proof and agree about success, tactic classification, and replay.
- `ProofReplayPlan`, mutable `SurfaceReplay` certificate recording,
  `is_surface_expressible()`, and internal-only tactics classified as simple are
  removed once migration is complete.
- Existing focused expansion regressions, including the field-effect
  definedness case, pass without heuristic simple replay or changes to C.
