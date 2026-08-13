# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases belong in explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`, with a corresponding issue here.

Click's adoption boundary is existing C source. For code inside the supported
C semantics, changing implementation behavior, control flow, helper routing,
redundant operations, or identifier spelling solely to make verification pass
is itself a verifier issue. Preserve the original source pattern in the
regression and fix Click. The only exceptions are independently desired program
changes, actual C bug or undefined-behavior fixes, and documented
semantics-preserving C0 desugaring.

Do not normalize verifier or tooling failures as part of proof development.
When work exposes an engine problem, either fix it with a focused regression in
the current chunk or write an issue before continuing. These problems take
priority over new language features and over making an example pass. Restore a
green, check-in-ready checkpoint before resuming the paused feature. In
particular, always track:

- a tactic that crosses its class budget, even if a larger command eventually
  finishes;
- a search that reports success but whose emitted or internal certificate does
  not replay;
- `click profile`, `click expand`, and `click audit` disagreeing about the same
  proof site;
- diagnostics large enough to obscure the actionable cause;
- proof scripts that must preserve irrelevant spellings or route calls through
  artificial helpers to compensate for verifier behavior; and
- a kernel/resource-model error discovered while building an example.

Smart-search incompleteness is not on that list. A smart tactic is a bounded,
best-effort proof search, and failing to find a certificate is an expected
result. Continue by splitting the proof into smaller operations or by naming
the relevant premises with simple tactics. File an engine issue only when the
search misses its bound, gives an unusable diagnostic, succeeds without a
replayable certificate, behaves unstably, or exposes something the simple
proof language cannot express. Do not retune shared heuristics solely to make
one large smart tactic pass.

Classify tactics by whether they select a proof rule, not by whether the user
listed their input facts. A tactic that receives hints and chooses among
normalization, rewriting, arithmetic, transport, framing, or other theories is
smart and must expand. A simple tactic checks one named rule from explicit
evidence with work proportional to that certificate. Simple replay must not
fall through alternate strategies or reconstruct a proof from ambient history;
if expansion cannot express the selected rule, that is a certificate-language
issue.

Use the [proof-failure triage guide](../docs/advanced/proof-failure-triage.md)
before filing an issue. It is the canonical distinction among ordinary proof
development, documented limitations, ergonomic automation problems, missing
functionality, correctness bugs, and tooling reliability bugs.

The issue should contain a small intended regression, the violated invariant,
and acceptance criteria. Do not leave the only reproduction in an uncommitted
large example or quarantine a regression without its issue.

Expansion is deliberately not a repair operation for a broken proof. The
selected proof unit and the contracts it depends on must verify before `click
expand` will emit a rewrite. In particular, a failure later in the same proof
blocks expansion of an earlier tactic. First restore correctness with ordinary
proof steps; then profile and expand the green proof. Broken proof units must
not be moved between partially checked intermediate states under an expansion
label.

The same ordering applies to profiling. A prompt correctness failure should be
fixed before performance analysis. Profiling an incomplete target is reserved
for diagnosing a timeout or unexpected slowness that prevents a green run; its
partial timings are not expansion candidates.

## Partial correctness and recursion

Click's C contracts now use partial correctness consistently: concrete
execution is separate from modular verification, and safe functions need not
have a return frontier. The `perpetual-service` example demonstrates that
boundary with an opaque step call and composite ownership.

Recursive C contracts are partial by default, while recursive pure Click
functions now require a checked `decreases` measure because they must produce a
value. Optional C termination now uses separate kernel-checked `decreases`
evidence and does not block ordinary recursive verification.

A true input-stream example remains a later design problem. Click can presently
prove safety invariants for an indefinitely running loop, but it has no event
trace, external-input, fairness, or productivity semantics with which to state
the interesting stream-processing guarantee. A true stream example is
intentionally deferred until those semantics exist.

## Recursive-function roadmap

The base recursion model, the `recursive-zero-list` integration example, its
composition audit, structural C termination, and explicit pure theorem
induction are in place. Their durable behavior is documented in the language,
kernel, proof-tactic, and pure-function guides. There are no open recursion
roadmap issues at present.

Keep one file per independent open problem. Put durable implementation design
in `docs/`, and delete an issue when its fix, regression coverage, and
documentation land.

## Verification performance burndown

The governing invariant is [Verification Efficiency](../docs/advanced/verification-efficiency.md).
Work these independent issues in dependency-aware order:

1. [Add deterministic scaling gates for simple verification](verification-scaling-benchmark-gate.md).
2. [Index proof facts and surface spellings](indexed-proof-fact-and-surface-spelling-stores.md).
3. [Replace pairwise resource-context work with indexed algebra](indexed-resource-algebra-avoids-pairwise-context-work.md).
4. [Remove context-wide proof minimization and contradiction scans](proof-derivation-avoids-context-wide-scans.md).
5. [Give verifier caches stable shallow identities](stable-content-identities-for-verifier-caches.md).
6. [Share checked replay authority between smart tactics and the expansion gate](smart-proof-search-and-expansion-gate-share-checked-replay.md).

The first issue establishes the measurement gate. Items 2--6 can then land as
separate green chunks with an asymptotic regression each. Checked execution
reuse across proof and contract certification is complete and documented in
the governing efficiency guide. Use
[owned-string](owned-string-exceeds-interactive-verification-budget.md) and
[owned-vector](owned-vector-exceeds-interactive-verification-budget.md) as the
full-project integration workloads; their wall times corroborate the scaling
gates but do not replace them.
