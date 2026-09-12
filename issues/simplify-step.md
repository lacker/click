# Make `step` simple across a call precondition

## Objective

`step()` is a simple tactic, not a smart tactic. Remove unretained prerequisite
derivation from its statement checking. A bare `step()` must either use an
exactly stated prerequisite or return a structured unmet requirement. A smart
caller such as `execute()` or `execute_until()` may construct an ordinary
checked `have`, then retry the same step. Expansion must show that `have` and
all of its witnesses,
transports, branches, and simplifications; the expanded proof must verify
cold without repeating hidden planning.

This is a verifier change. Production C stays unchanged, and no proof-only C
rewrite, no-op branch, or alternate implementation is acceptable.

## Invariants and design constraints

The proof engine must preserve exact source provenance at the two seams where
the current representation loses it:

1. the caller requirement whose entry facts are projected by `Choose`; and
2. the C access occurrence that produced a generated load equation.

These are presentation/planning metadata, not proof authority. They may select
the source record that an ordinary checked operation names, but they may not
make a fact available, equate snapshots, choose a logical branch, or discharge
a goal.

Use typed identities with separate lifetimes:

```text
CallerSourceOwnerId = (ordinary function, canonical source unit, declaration)
RequirementSourceId = (CallerSourceOwnerId, outer requirement ordinal)
LoadSourceId = (C source owner, source region, access occurrence ordinal)
```

Actual arguments, binder substitutions, and memory snapshots are per-use
validation data, not part of a declaration/access identity. IDs are minted
before lowering erases the relevant distinction and are deterministic from
canonical source ownership and documented declaration/occurrence order.

All provenance lookups must be bounded and fail closed:

- use shallow indexes with bounded candidate buckets; never scan unrelated
  facts, requirements, functions, or memory history;
- keep exact expressions and snapshots for collision validation, not as deep
  hot-path map keys;
- reject missing, duplicate, overfull, stale, wrong-owner, wrong-argument,
  wrong-binder, wrong-epoch, or ambiguous provenance;
- share immutable tables between proof branches and apply output-sized deltas
  at forks and joins; and
- keep IDs, tables, events, and resolutions out of proposition meaning,
  contract/theorem identity, and ordinary certificate serialization.

Expanded proofs contain only ordinary Surface Click operations. The ordinary
checker remains the authority and must not consult source metadata to accept a
certificate.

## Status at the implementation pause

The caller-requirement vertical is complete. The dynamic C-string path retains
an ordinary checked proof using exact caller source identity rather than
reconstructing a requirement from the final fact vector.

The generated-load foundation is also landed and green:

- parsed scalar field accesses have deterministic source identities;
- exact generated-load/source observations travel through execution;
- conflicting observations produce persistent ambiguity tombstones;
- branch forks and joins retain output-sized event suffixes; and
- only accepted cursor transitions commit source observations.

The last green checkpoint is `266d0d44`. `scripts/check.sh` passed there with
2,831 tests and all 14 fixture gates. There is no pending implementation diff.

The next checkpoint is deliberately narrower than the rest of Phase 2: build
an immutable per-function source-load plan. Given a `LoadSourceId`, it must
return exactly one source field spelling, position, containing statement, and
validation record for the source-side pointer/type/offset. It must be built
alongside C0 lowering, shared between proof branches, and queried without an
AST walk or ambient scan. The current event identity contains only source unit,
function, and occurrence, so no load-equation consumer should land before this
plan supplies and validates the missing region and spelling data.

After that checkpoint, reassess the representation before implementing the
`owned-string` and `bounded-pool` consumers. Do not combine the source-plan
design, both consumers, and the Planning cutover into one change.

## Phase 1 — caller requirement identity (complete)

### Landed boundary

The proof context now builds a caller requirement index while constructing the
initial claim context. It preserves an `EntryFactOrigin` alongside lowered
entry facts, so the source declaration is not reconstructed by comparing or
slicing the final fact vector. The index record keeps distinct:

- `RequirementSourceId` and outer declaration ordinal;
- the lowered principal fact index and exact fact;
- the bounded connective/projection token;
- source arguments and the caller entry snapshot.

The Phase 1 query is deliberately narrow:

```text
lookup_unique_caller_requirement(
  owner, predicate, argument_slot, caller_parameter_slot,
  source_arguments, expected_entry_snapshot
) -> unique selection | none
```

It supports an ordinary caller function, a direct concrete call, and a
top-level predicate requirement whose selected argument is a direct caller
parameter. It resolves the exact callee source clause already selected by the
unmet carrier, substitutes the checked call arguments, and maps that argument
to the caller's parsed parameter. It does not infer the caller ordinal from a
callee ordinal or from the generated kernel proposition.

`Choose` remains proof authority: it revalidates the selected source ordinal,
fact, binder substitution, and active entry snapshot, then retains the
projection. Source IDs only make that exact ordinary operation constructible.
Unsupported labels, nested/resource/generated forms, callbacks, generic
wrappers, ambiguous candidates, and stale positions fail with the original
structured requirement.

The dynamic C-string regression retains a checked `have` containing ordinary
`Choose`, `Witness`, explicit transport, and coverage operations. It uses a
nonzero requirement ordinal, unrelated entry facts, and an alternate pointer
name. Its expansion contains no smart operations and verifies cold without
logical Planning.

## Phase 2 — generated-load source occurrence identity (foundation complete)

Continue from the landed runtime event channel on a fresh integration branch.
The remaining `bounded-pool` and `owned-string` obligations need faithful
source expressions for equations such as:

```text
Var(load_variable) == load(snapshot, pointer)
```

`LoadSourceId` is now minted before C access syntax is erased, and the
evaluated load emits a source event when it mints the exact
`GeneratedLoadBinding`. Events travel through the ephemeral expression,
argument, statement, and transition paths into a persistent transition-local
resolution:

```text
Variable -> Unique(exact binding, source use) | Ambiguous
```

The variable is only a shallow lookup key. A different binding or source for
the same variable creates a permanent ambiguity tombstone; identical pairs
are idempotent. Forks share roots, joins consume arm suffixes, and failed
retries record nothing. The source-independent `GeneratedLoadBinding` type
does not change.

What remains is the aligned source plan beside the kernel
expression/statement. Every shape-changing rewrite, including synthetic
nodes, must create or explicitly omit its plan node at the same time. A
reconstructed preorder walk is not acceptable.

A Surface consumer must validate variable, binding, source owner/region/
occurrence, instantiated spelling, statement-entry selector, memory identity,
and exact re-lowering before constructing the ordinary `have`. Missing or
stale provenance, conflicting accesses, wrong epochs, synthetic/misaligned
nodes, or an unfaithful spelling fail closed. No pointer/name/hash heuristic
or ambient proposition scan is an alternate route.

Root owns the lowering/event interfaces and generated-binding integration. A
Luna task may own only source-plan propagation and deterministic scaling
tests; after integration, another Luna task may own only the Surface sidecar
consumer and reduced real obligations. An independent Luna review must audit
ambiguity, epochs, cold expansion, and output-sized fork/join behavior before
the vertical commit is merged.

Required evidence is one unchanged real obligation from each load-equation
example, with a faithful equation that lowers to the exact proposition at the
correct memory point, expands to an ordinary retained `have`, and verifies
cold. Identical-looking accesses at different locations, conflicting source
occurrences, stale provenance, and another epoch must fail closed.

## Phase 3 — orchestration and census

Root owns this serial phase because it changes retry routing and the smart
execution state machine.

1. Re-run the hidden-`Planning` census on the current integration base,
   including logical derivations reachable through `Contextual`; do not rely
   on historical counts.
2. Route every supported requirement through exact evidence or one of the two
   source-identity paths. Every smart success must retain an ordinary proof.
3. Cover disjunctive, sequential, and multi-requirement calls, selected
   contracts/callbacks, branches, `execute_until`, scoped execution, and
   ordinary explicit `step`. A bare step in the minimal disjunction regression
   must return the structured obligation without logical Planning.
4. Keep legitimate exact condition evaluation and explicit transport. Unsupported
   shapes must fail promptly with the original structured requirement.

Luna work in this phase is review and targeted regression additions only; no
parallel agent may change the shared retry policy while root is integrating
the census results.

## Phase 4 — cutover and removal

Only after Phases 1--3 are green on one base:

1. Remove unretained logical prerequisite derivation from simple call
   checking, preserving exact checks and explicit transport that do not search
   for propositions.
2. Verify that simple `step()` either finds an exact prerequisite or returns
   the structured refusal, while only smart callers construct retained proofs.
3. Expand and cold-reverify the complete affected corpus, including dynamic
   C-string and both load-equation examples.
4. Run the unfiltered gate with the body-rerun census at zero.

Root owns the cutover, final authority-boundary audit, merge, and push. A Luna
reviewer examines the exact green commit read-only immediately before merge.

## Acceptance criteria

- Bare `step()` performs no unretained logical prerequisite derivation or
  Planning search.
- Smart execution retains every constructed prerequisite as an ordinary
  `have` before the owning call.
- Expansion exposes all proof operations and verifies cold through the normal
  entry point.
- Removing a required generated `have` or transport fails in a minimal
  regression.
- Caller requirements and generated loads use typed, exact, fail-closed
  provenance with no ambient scans or semantic source heuristics.
- Wrong owner, argument, binder mapping, source occurrence, or memory epoch
  cannot authorize a proof; alpha-renamed binders remain valid.
- Production C remains unchanged.
- The affected corpus passes with no hidden prerequisite derivation,
  `scripts/check.sh` passes unfiltered, and both fixture harnesses report zero
  body reruns.
- Verification remains approximately linear, up to indexed lookup factors,
  in source and certificate size.

## Stop and revise

Pause the phase and redesign if implementation requires ambient scans,
first-match selection, display names, pointer/hash inference, merged epochs,
deep hot-path keys, metadata that grants facts, a new trusted proof rule, an
unverifiable certificate, expansion that disagrees with ordinary checking, or
unexpectedly slow verification. Restore the worktree to the last green
checkpoint before changing direction.

## Not in scope

- recursive-call `decreases` obligations;
- completeness of smart proof search;
- proof syntax introduced only to recover source identity; and
- changes to verified C made only to simplify a proof.
