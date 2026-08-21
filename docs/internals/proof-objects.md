# Proof objects

Click represents accepted proof work as deterministic simple steps rather than
trusting the search procedure that found them.

## Surface proof and certificate types

`SourceProof` distinguishes an omitted proof, a smart proof request, and an
explicit tactic block. Parsed tactic statements become `ProofTactic` values.
Each tactic has a `TacticClass` used by checking, instrumentation, profiling,
and expansion.

After proof construction, `ProofCertificate` stores a sequence of
`SimpleProofStep` values. Steps identify nested branch or structural positions
with `CertificatePathSegment`; this keeps a certificate's operation attached
to the proof state in which it was produced. A certificate can be rendered
back to surface tactics for expansion.

## Replay state

The replay state combines logical and execution state. It owns the available
surface-to-kernel fact mappings, symbolic C execution frontier, resources,
marks, focus, and structural context. A replayed step must resolve its
selectors in this state and justify the requested transition through checked
operations.

Control-flow proof objects preserve structure rather than flattening every
branch into an unrelated list. Branches carry path-local assumptions;
continuations identify where common execution resumes; joins require compatible
facts and resources. Loop certificates correspond to initialization,
preservation, and exit obligations rather than a fixed unrolling.

## Smart planning

Planning modules can inspect a state, rank candidate steps, and explore within
deterministic budgets. They return candidate simple transitions through the
same certification boundary used by explicit tactics. A candidate is not
accepted merely because the planner labels it successful.

The replay pipeline reconstructs the initial claim state and applies the
certificate. Failure is attributed to the selected fact, program point,
resource, or path when possible. Expansion uses only a successfully replayed
certificate.

## Kernel proof objects

Kernel structures in `src/kernel/primitives/proof_objects.rs` represent
primitive semantic evidence and obligations. They are separate from the
surface certificate: surface proof steps encode user-reviewable operations,
while kernel objects justify the underlying proposition, execution, memory, or
resource transition.

Important invariants are:

- all accepted smart work has a replayable simple certificate;
- selectors resolve against the state at their certificate path;
- proof checking doesn't depend on failed-search history;
- expansion preserves proof-site identity and emits verifiable Surface Click;
- persistent proof-state sharing must not permit mutation of an earlier state;
- instrumentation can observe work but cannot change the validity decision.

The former chronological proof-object design log is preserved at
`design/proof-object-api.md`; this page describes the current architecture.
