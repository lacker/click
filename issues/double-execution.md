# Eliminate double execution

## Current state

Click normally executes C statements once, through checked proof-object
operations, and retains the resulting kernel-issued transition evidence. At
function exit the kernel can seal that retained trace into the checked function
execution used by claim and contract certification. Existing zero-rerun
regressions cover straight-line proofs, explicit C branches, proof-level case
partitions, shared continuations, verified and concretely executed loops,
post-execution resource folds, nested resource scopes, counted resources, and
`branch ensuring` interfaces.

Two fallback mechanisms still execute a function body independently after its
proof-directed execution:

1. In `finish_ordered_proof` (`src/surface/proof/claim_proofs.rs`), claim
   finishing calls `checked_c_function_execution_from_proof_evidence`
   (`src/kernel/api.rs`) and, whenever that sealer returns `None` or one of
   three explicit guards fires, selects `cached_independent_execution`.
2. At the opaque-contract boundary
   (`prove_c_function_contract_execution_paths_with_checked_artifacts`,
   `src/kernel/api.rs`), final certification reuses an exact,
   resource-rebased, or exhaustive entry-partition checked artifact when it
   can. If none matches, it silently falls back to fresh symbolic execution of
   the function body.

Consequently, one proof can still perform its proof-directed statement
execution, an independent claim execution, and another contract-finalization
execution. The independent-execution cache reduces repeated work but preserves
the wrong architecture. It can also produce the characteristic failure in
which proof construction succeeds but a later execution cannot reproduce it.

The proof object already retains statement theorems, checked branch structure,
proof-case partitions, resource representation transitions, and function-entry
resource materialization. Do not redesign those completed parts merely to
remove the remaining fallbacks.

The arena example verifies through nested `arena_region` and `arena_metadata`
scopes, but its sidecar does not yet contain the intended explicit
`arena_write` contract. That contract remains the end-to-end resource-shaped
acceptance case.

## Where the reruns actually happen

Measured on 2026-09-01 over all 426 mdtests and the 14 example projects; the
numbers are the ratchet baselines pinned in `tests/mdtests.rs` and
`tests/examples.rs` (slice 1), keyed by `instrumentation::SealRefusal` and
`instrumentation::ContractFallback`.

Claim finishing reran a body 100 times in 83 mdtest fixtures and 48 times in
the examples. The three guards are the minority; most reruns happen because
the sealer refuses the retained trace:

| Cause of a claim rerun | `SealRefusal` | mdtests | examples |
| --- | --- | --- | --- |
| Loop step theorem carries exit hypotheses (invariant at the fresh head variables, e.g. `V1000000 <= n`) that the path's exact facts do not list, so `proof_evidence_premises_are_retained` fails | `UnretainedPremise` | 28 | 11 |
| `return` from a nested statement while body tail remains, or a diverging loop; `seal_proof_evidence_events` refuses any `Return`/`VerificationDiverges` outcome with a tail | `ReturnWithTail` | 22 | 6 |
| Proved statement or entry memory differs from the running sealed state: memory snapshot identity on heap fixtures; loop-clause-bound `while` statements | `StateMismatch`, `StatementMismatch` | 7, 3 | 4, 0 |
| Proof-case partition or path count differs from the evidence traces (proof `if` cases, outcome forks) | `CasePartition`, `PathCount` | 4, 3 | 12, 0 |
| Guard: counted entry closed implicitly by outcome `simp()` rather than an explicit `frame()` | `ImplicitCountedClose` | 20 | 3 |
| Guard: outcome proof with an unfolded predicate | `OutcomeUnfold` | 11 | 10 |
| Guard: quantified resource fold or close after C execution | `QuantifiedResourceClose` | 2 | 2 |

Contract certification reran a body 40 times in 34 mdtest fixtures and 34
times in the examples. Every one of those had a same-function artifact from
claim finishing available. Two causes account for all of them
(`ContractFallback`: mdtests 19 predicate, 11 resource, 2 other premise, 8
entry-state delta; examples 3, 11, 5, 15):

- The artifact's assumptions include one premise the reconstructed contract
  context cannot derive: the opaque `Predicate` identity of a `requires`
  clause (`valid_pool`, `first_is_seven`, `terminated`, ...) that contract
  certification lowers operationally into its body, or an entry
  `CResourceContains` fact of a composite definition.
- The artifact's entry state differs from the contract entry state only in
  `resources` and `counted_populations` (the claim proof opened or unfolded a
  resource at entry) and the resource rebase did not apply.

Fixture lists per row are reproducible from the instrumentation described in
slice 1; do not keep the fixture lists in this file.

## Violated invariant

A completed checked proof object is the execution evidence for the function it
proved. Ordinary verification must not secretly execute the same C body again
to decide whether that proof was valid.

Every proof-object operation must check its explicit premises and return a new
valid proof object. At function exit, sealing composes those already-checked
operations. It may validate lineage, source order, exhaustive branch coverage,
and exact state compatibility; it must not reconstruct the proof by executing C
again or by re-proving accumulated facts from an ambient context.

If a checked operation lacks information required by later composition, retain
the smallest output-sized identity or state delta when that operation succeeds.
Reject a mismatched transition at the operation or join that creates it. Do not
hide the mismatch behind independent execution.

## Kernel and tactic boundary

The proof object itself is the checked authority. Do not introduce a parallel
fact-derivation or certification representation that must later be aligned with
the proof object. In particular, removing double execution does not call for a
`CheckedFactDerivation`-style database of facts to be proved a second time.

Smart tactics may search or plan and then emit explicit simple proof steps.
Simple steps and final sealing must remain deterministic and fast. Their kernel
checks may use narrow decision procedures appropriate to the explicit rule,
but they must not recover a missing premise through general ambient
disjunction splitting, unrelated theorem search, or recursive reconstruction
of the proof context.

Per-path state should have one canonical checked representation. Avoid parallel
vectors of facts, conditions, snapshots, and evidence whose correctness
depends on positional alignment. Persistent sharing and output-sized deltas are
appropriate; cloning or rescanning accumulated path history per operation is
not.

## The approach

The sealer builds the certified execution path by path from the proof
object's own candidates, zipped in order. Where it succeeds, the certified
execution is a restatement of the proof, and the outcome pairing
(`outcomes_match`), `certify_c_function_execution_path_resource_representation`,
and `describe_function_outcome_delta` are alignment between two copies of the
same thing. Where it fails, exactly one proof-object operation failed to
retain an output-sized delta, or the sealer is stricter than the operation
that produced the event.

So the work is not to type all evidence at once and not to build a fact
database. It is to make sealing total over the corpus one refusal class at a
time, behind a ratchet, then delete the alignment code, then make the
contract boundary consume the sealed artifact structurally. At the end the
trusted theorem for a claim is composed from the proof object's retained
kernel theorems and its closed outcome goals, and `finish_ordered_proof`
reduces to sealing plus reading those closures.

Order the slices by cost: slices 2 through 5 are each smaller than any of the
three guards and remove two thirds of the reruns. Every slice must be
independently green, must lower at least one ratchet count, and must delete
the guard or fallback it replaces. Do not accumulate a second implementation
alongside the old one.

## Implementation slices

### 1. Typed refusals and a ratchet (landed 2026-09-01)

`checked_c_function_execution_from_proof_evidence` and
`seal_proof_evidence_events` return `Result<_, SealRefusal>` with one variant
per refusal site; the three claim-finishing guards record into the same
enum; the contract-boundary fallback records a `ContractFallback` cause.
`instrumentation::take_body_rerun_census` collects both, and the mdtest and
example harnesses compare the unfiltered corpus census with pinned baselines
in both directions (`docs/internals/testing.md`, "Body rerun ratchet"). Each
later slice lowers a pin to its new value. Fixture lists per reason are
reproduced by adding a temporary `eprintln!` at `record_seal_refusal`; they
do not live in this file.

### 2. Return with a remaining tail (landed 2026-09-01)

On a `Return` or `VerificationDiverges` statement outcome the sealer drops
the unconsumed tail instead of refusing: the path has ended and the tail is
unreachable on it. A trace that continues past that outcome, or a `Normal`
outcome that leaves source unexecuted, still refuses as `IncompleteTrace`
(kernel tests in `contract_execution_tests.rs`; surface regression
`early_return_seals_without_a_body_rerun`). `ReturnWithTail` fell from 22 to
0 over the mdtests and from 6 to 0 over the examples; 16 and 2 of those
proofs now seal, and the other 6 and 4 reach `StatementMismatch`, which
slice 4 owns.

### 3. Loop exit hypotheses

The verified-loop step's theorem is `hypotheses -> CStatementVerifies(...)`
whose hypotheses are the invariant at the fresh head variables and the negated
condition. They are justified by the loop rule and are assumptions of the
exit path, not facts to derive. Retain them at the loop step as the path's
exact facts (the candidate's `execution_facts`), so the sealer finds them
through the existing exact lookup. Do not widen
`proof_evidence_premises_are_retained` to ambient derivation. Negative test:
a forged exit fact that is not one of the rule's hypotheses is refused.
Clears the first row.

### 4. State and statement identity

Two sub-causes. Heap fixtures: the proved statement's entry memory and the
sealed running memory differ in snapshot identity only; find which side
canonicalizes and compare canonically at the operation that records the
theorem, not in the sealer. Loop-clause-bound functions: the frontier
function differs from the checked function in its `while` statements; seal
against the frontier function, and keep
`proof_evidence_function_refines_same_source` as the guard that the two
functions differ only there. Clears the third row.

### 5. Partitions and path counts

Outcome case splits that fork undecided paths and proof `if` cases leave more
candidates than evidence traces, or a partition the sealer cannot match. The
fork or split must record its partition in every trace it creates, at the
operation, so `proof_case_partitions_match_paths` and the path count agree
by construction. Clears the fourth row.

### 6. The three guards

In this order, each deleting its guard immediately:

- Implicit close. The implicit closer of a counted entry must publish the same
  checked frame transition an explicit `frame()` records
  (`CheckedFrameAuthority`), through one code path. Negative test: a forged
  exit population is refused without executing the body.
- Outcome unfold. Outcome `unfold(p)` must apply the sealed unfolding theorem
  (`prove_c_function_contract_predicate_unfolding`, already used for entry
  unfolds through `function_entry_derivations`) to the outcome goal's exact
  facts, instead of pushing a name into `unfolded_predicates` for
  `unfold_available_predicate_facts` to re-expand ambiently at finishing.
  Negative test: an unfolding whose body is not the registered one is
  refused.
- Quantified fold or close. Extend `CheckedResourceRewrite` (or add a sibling
  event) with a kernel-checked counted-population delta, using the same rule
  that certifies contract resource effects at a frame. Negative test: a
  changed population count without the rule is refused.

### 7. Delete the fallback and the alignment

When every ratchet count is zero: remove `cached_independent_execution`, the
`certification_cache`, and the three guards; a sealing refusal becomes the
proof's diagnostic. Then, because sealed paths are zipped with the proof's
candidates, replace the outcome pairing with index identity and delete
`outcomes_match`, `certify_c_function_execution_path_resource_representation`
and its cache, and `describe_function_outcome_delta`. Keep the execution
counter as regression instrumentation. This is the slice where a completed
proof object is, by construction, the execution evidence.

The remaining kernel-API-only audit bugs (claim coverage and injected entry
facts in [contract-rule-trust-boundary.md](contract-rule-trust-boundary.md),
sequential binder substitution in
[kernel-binder-hygiene.md](kernel-binder-hygiene.md), and
[call-havoc-fingerprint-collision.md](call-havoc-fingerprint-collision.md))
are masked only by the exact checks and re-execution this slice removes. Land
them before it.

### 8. Contract boundary

With every claim supplying a sealed artifact, make artifact reuse structural:

- A premise that is the registered predicate identity of one of the
  function's own `requires` clauses is authorized; the kernel already holds
  the predicate-to-body pairs in `predicate_unfoldings()` and reconstructs the
  body operationally, so the identity is a renaming of an assumption it has.
- An entry `CResourceContains` premise derivable from the function's composite
  definitions at the contract entry state is authorized.
- An entry state that differs from the contract entry only in `resources` and
  `counted_populations` is rebased through the artifact's retained
  `CheckedFunctionEntry`; find why `rebased_reuse` currently declines these
  and repair that check rather than widening it.

Then delete the `(None, None, None)` body-execution arm: an artifact that
still cannot be reused is a local evidence error naming the premise or state
component that blocked it.

### 9. Arena acceptance contract

Add the intended `arena_write` contract to `examples/arena/arena.click`, keeping
the existing C unchanged and its mutable footprint narrow. Its nested resource
scopes must verify with zero independent whole-body executions.

## Not in scope

The following are intentional independent checks, not double execution in this
sense:

- `click expand` verifies the rewritten source artifact it emits;
- `click audit` cold-verifies original and rewritten artifacts;
- expansion regressions independently verify serialized proof text; and
- an opaque function call applies its installed rule without executing the
  callee body.

This issue does not require new surface syntax, changed C semantics, rewritten
C, a general proof-object redesign, or removal of search from smart tactics.

## Acceptance criteria

- `finish_ordered_proof` contains no independent whole-function execution,
  independent-execution cache, or outcome pairing; sealing is the only source
  of the certified execution and its paths correspond to the proof's
  candidates by index.
- Opaque-contract certification never executes a supplied proof's function
  body when artifact reuse fails; it reports a local evidence error.
- A completed proof seals its existing checked proof-object state directly;
  finalization does not re-prove accumulated facts.
- Simple checks added or used by this migration, and final sealing, perform no
  ambient case search and remain approximately linear, up to logarithmic
  indexes and output-sized deltas, in selected C, Click, proof state, and
  certificate size.
- The ratchet census reads zero for every refusal variant and stays in the
  test suite; each removed fallback shape has a negative test showing forged
  or mismatched evidence is rejected without executing the body.
- The explicit `arena_write` contract verifies without changing its C source,
  weakening resource semantics, or adding proof-only C structure.
- Documentation describes proof-directed execution as the sole ordinary
  verification model while preserving the intentional independent checks
  listed above.
- `scripts/check.sh` passes.
