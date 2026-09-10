# Keep proof search out of kernel authority

## Status

This is a P1 architectural umbrella. Most of the original cleanup is complete:
the duplicate certification and evaluation routes, production environment
switches, dead fallbacks, general finite context splitting, contextual
canonicalization, global load-equality search, and the old fuel and structural
depth cuts have been removed. Smart loop closure, branch interfaces, resource
deltas, and quantified matching now retain checked local evidence.

The remaining work is to migrate the authoritative consumers of the general
proposition prover listed below. The arithmetic migration is a separate P1
implementation issue in [arithmetic.md](arithmetic.md), and blocks completion of
this umbrella.

## Invariant

The kernel checks; it does not plan or search for proofs.

An authoritative kernel operation may apply a fixed collection of exact rules,
traverse the explicit input or certificate it was given, and use indexed
lookups into ambient state. Its work and completeness must not depend on opaque
fuel, recursion-depth, or retry limits. Failure of a local rule must not launch
candidate selection over unrelated facts, recursive proof attempts, or an
alternate global reconstruction.

Search belongs to Surface Click smart tactics. A smart tactic explores
persistent proof descendants only through the same checked operations available
to explicit proofs. Success is a completed checked descendant with provenance
that `click expand` can render as parser-accepted Surface Click and independently
verify through the ordinary entry point.

This boundary uses three distinct representations:

- The kernel `ProofObject` is immutable semantic proof state and a branch
  cursor. It is not a serialized proof history.
- Surface proof provenance records the checked operations that produced a
  descendant.
- `ProofCertificate` is the source-expressible serialization used for expansion.
  It contains no smart or internal-only leaf.

Typed kernel evidence may justify the semantic work behind one simple Surface
step. It need not print every internal node, but its checker must be local and
deterministic, and the enclosing Surface step must remain source-expressible and
recheckable. "Simple" therefore means locally checkable, not constant-sized: a
step may traverse one named C statement, term, schema, resource definition, or
explicit certificate.

"No fallback" means no broader proof-search fallback. It does not prohibit a
short deterministic sequence of exact rules over named inputs. Syntactic
equality followed by an indexed lookup is one exact check. Enumeration is also
valid when the operation or certificate explicitly names the enumerated input
and work is charged per item.

A search that constructs a derivation and then checks it inside `src/kernel/`
is still kernel proof planning when its result issues a theorem, discharges an
obligation, prunes a required execution path, or advances a proof object.
Checking the discovered derivation establishes soundness; it does not establish
the intended planning/checking boundary.

Structural walks must be complete over their named input, cycle-safe where
necessary, and iterative where Rust stack depth is a concern. Fixed memo
capacities may affect performance but not answers. Execution path, loop-unroll,
and call-depth budgets are semantic execution capacity and remain separate.
A wall-clock or deterministic-work deadline is crash containment: expiry must
surface as a verification-limit error and must never be cached as a negative
logical answer.

## Remaining authority boundaries

The inventory below is organized by consumer, not by occurrences of
`PureFactContext::proves`. A grep is a useful audit aid but does not distinguish
proof authority, exact theory checks, planning metadata, and redundant-output
suppression.

### Context-free normalization

`proof/fact_reasoning.rs::normalizes_context_free`, used by `normalize` and by
guard and instance checks, tries atomic derivation and then the general
derivation builder even though the ambient context is empty. Empty context does
not make recursive logical proof construction a normalization rule.

Separate input-bounded definitional reduction from logical proof construction.
Keep exact normalization in the kernel; require explicit logical steps for any
remaining closure.

This migration is in progress. The first three green slices make top-level
conjunction, disjunction, and implication explicit proof boundaries for
`normalize` and `normalize using`. Smart proofs retain `both` scopes for
conjunctions, a checked arm followed by `left` or `right` for disjunctions, and
`intro` followed by a checked consequent proof for implications. Saved
expansions spell those choices instead of relying on the kernel to reconstruct
them. Quantifier construction and logical construction nested under quantifiers
still need the same treatment before this boundary is complete.

#### Quantifier migration prerequisites

An abandoned prototype established that rejecting `ForAll` in the normalization
leaf is mechanically small but exposes older Surface/lowering seams. Do not
repeat that change as a single fixture-migration patch. Fix these prerequisites
first, each as a coherent green change. No implementation from that prototype
landed; the notes below are the retained result.

- A written proposition and its lowered kernel goal are not necessarily
  isomorphic. Lowering can insert loadability and definedness implications that
  have no Surface connective. `intro` must distinguish those guards from a
  written implication using exact lowering provenance; it must keep the written
  Surface goal focused while hidden guards are introduced.
- Universal introduction must retain the exact binder substitution used by the
  kernel. Pure-proof lowering, fixed-state lowering, `extract`, arithmetic
  premises, and contradiction citations must all consult that retained binding
  rather than independently choosing or reconstructing a binder.
- Introducing an implication changes the fact context. Re-lowering its written
  antecedent afterward can produce zero paths when the antecedent is
  inconsistent, even though the already-lowered kernel antecedent is the exact
  fact that `intro` added. Retain the checked Surface-to-kernel antecedent and
  its structural subfacts at introduction time; do not rediscover them by
  re-lowering under the changed context.
- Loop initialization currently has a path that removes already-known leading
  implications while planning an invariant proof, then serializes that proof
  inside a combined certificate whose independent checker sees the complete
  obligation. Construction and independent verification must use the same
  exact goal. If a lowering guard is part of the checked obligation, its
  discharge must appear in the retained certificate rather than being silently
  removed only during planning.

These are provenance and goal-identity requirements, not invitations to add
new kernel reasoning. In particular, do not pair a Surface antecedent with a
kernel antecedent merely because their logical constructors have the same
shape after lowering failed. Do not synthesize a negated kernel fact from a
remembered positive fact. Both approaches make certificate text cease to be an
exact account of the checked proposition. The correspondence must come from
the successful lowering that created the obligation or from a checked
structural refinement of that retained correspondence.

The failed prototype passed a small pure theorem with `forall`, implication,
conjunction, and disjunction, but the full library exposed quantified memory
invariants and vacuous arithmetic guards. The next implementation must cover at
least these cases before changing the normalization leaf:

- a pure universal whose body nests implication, conjunction, and disjunction;
- a vacuous quantified implication such as
  `0 <= k and k < 0 implies ...`, expanded into explicit checked introductions
  and cited leaf evidence;
- quantified memory predicates such as `all_le_range`, including the hidden
  loadability implications introduced by lowering;
- loop-entry and loop-preservation certificates such as the bubble-sort and
  `copy3` fixtures; and
- quantified outcome proofs that retain their selected instantiations and
  transports.

For each case, verify the smart source, inspect the expansion for explicit
`intro` and nested logical steps, parse and independently verify that expansion,
and check that deleting or reordering a required introduction is rejected. A
fixture edit that merely adds enough `intro` calls for one lowering context is
not sufficient: the same retained certificate must check at every site that
consumes it. Do not mark this migration complete until `scripts/check.sh`
passes.

### Pure-theorem authority

`api.rs::prove_universally_quantified_pure_implication` proves the conclusion
again from its requirements after the Surface proof has already been checked.
The `_by_int32_rewrites` variant names an ordered rewrite list but still proves
each equality from the requirements and invokes the general prover for final
closure.

Issue authority from the checked proof completion and explicit rewrite
evidence. The kernel must validate the exact requirements, variables, rewrite
order, conclusion, and completion without rediscovering a proof.

### Calls, refinement, and resources

Call and resource code in `functions.rs`, `primitives/resource_algebra.rs`, and
`primitives/contracts.rs` still uses general reasoning for guarded requirements,
footprint guards, refinement obligations, quantity relations, population
transitions, resource facts, and loop-rule prerequisites.

Migrate these by consumer. Retain explicit guard, quantity, containment,
separation, and refinement evidence with the operation that consumes it. Do not
replace the whole family with exact membership in one completeness-breaking
change; exact resource-algebra rules over named inputs remain kernel work.

### Lowering and execution

`spec.rs`, `reasoning/path_facts.rs`, and remaining helpers in `loops.rs` use
general reasoning to decide specification branches, overflow and loadability
obligations, invariant paths, segment containment, and whether facts or
obligations may be omitted.

Separate three cases before changing a caller:

- proof-relevant discharge or path pruning needs retained checked evidence;
- an unresolved safety condition should become an explicit obligation; and
- redundant-fact suppression may use only an exact local test, or be deleted.

The migration must not change the C merely to expose a friendlier proof state.

### Termination

`termination.rs::assume_structural_path`, `ranking_proves`, and
`ranking_proves_lexicographic_decrease` discharge structural-path and ranking
conditions with general and arithmetic reasoning. Lexicographic checking also
selects a pivot by trying alternatives.

Keep the named ranking expression or tuple as input, but move proof and pivot
selection to Surface planning. Retain the selected pivot and the checked
nonnegativity, equality-prefix, and strict-decrease evidence used to issue the
termination rule.

### Legacy theorem constructors and residual audit

The exported constructors
`prove_c_function_satisfies_specification_and_propositions` and
`prove_c_statement_executes_and_propositions` still prove arbitrary added
propositions. No non-test repository caller was found in the last audit. Delete
them if a fresh export and caller audit confirms they are unused.

After the named consumers are migrated, audit lower-level `decide`, atomic
theory, memory, and resource helpers transitively. A helper may remain only when
its authoritative result is an exact, local rule over named input. Merely
wrapping the general prover or moving proof construction to another kernel
module does not complete the migration.

## Implementation sequence

Each item should land as a coherent green change with its own focused and
scaling regressions.

1. Finish splitting context-free definitional normalization from logical
   derivation. Top-level conjunction, disjunction, and implication construction
   is explicit. Before rejecting quantified normalization leaves: (a) retain
   exact Surface/kernel binder and antecedent provenance through hidden
   lowering guards, (b) make loop certificate construction and independent
   verification use the same complete goal, and (c) migrate quantifier
   construction plus nested logical structure with the regressions listed
   above.
2. Retain checked pure-theorem completions and remove the second proof.
3. Delete unused legacy theorem constructors after confirming their callers.
4. Migrate call, refinement, and resource consumers one evidence type at a
   time.
5. Propagate lowering and execution obligations instead of proving or omitting
   them implicitly.
6. Retain explicit structural and numeric termination evidence, including the
   chosen lexicographic pivot.
7. Complete the transitive authority audit and the separate P1 arithmetic
   migration.

When a boundary has many callers, first run a temporary census that counts both
attempts and deciding successes. A successful fallback attempt does not prove
that a fixture needs it; rerun with only that route denied before designing new
evidence. Temporary probes and denial switches must not land.

## Regression requirements

- For every search moved outward, verify the generated explicit proof and an
  independently parsed expansion. Reject missing, reordered, substituted,
  wrong-arm, and unrelated evidence as appropriate.
- For every structural walk or indexed evidence checker, add deterministic
  multi-size regressions over the relevant input and unrelated ambient state.
- A simple check must have work bounded by its named input, indexed lookups, and
  produced state or certificate delta. It must not clone or scan the complete
  context.
- Deadline expiry must report a verification limit and must not populate a
  reusable negative memo.
- Preserve the original C and proof claim as the regression. Adapt contracts,
  tactics, evidence, lowering, or kernel rules rather than rewriting the C for
  the verifier.

## Not in scope

- Search performed by bounded Surface smart tactics that return checked,
  expandable proofs.
- Exact interpretation of a named C statement, expression, term, resource
  definition, or datatype schema.
- Execution path-width, loop-unroll, call-depth, and explicit smart-tactic work
  budgets.
- Memo capacity and eviction policy when eviction cannot change correctness or
  completeness.
- Performance work on an exact relevant-input-bounded rule unless a scaling
  regression shows that classification is wrong.

## Acceptance criteria

- No authoritative kernel result is obtained by ambient candidate selection,
  recursive general proof construction, speculative fallback, or a
  completeness-affecting fuel or depth cut. This includes completion of the
  separate arithmetic migration.
- Every remaining kernel rule has explicit named inputs and work bounded by
  those inputs, indexed evidence, and semantic output.
- Every smart success has complete provenance that expands to ordinary Surface
  Click containing only simple or structural operations, and the rewritten
  source verifies through the ordinary entry point.
- Pure-theorem, call/refinement, resource, lowering/execution, and termination
  authority uses checked retained evidence rather than rediscovering proofs.
- Deadline or exact-cycle interruption cannot escape as an ordinary proof miss
  or poison a negative memo.
- No production `std::env` read or search-disabling switch exists under
  `src/kernel/`.
- `scripts/check.sh` passes, both fixture harnesses pass with the contract
  fallback census at zero, and deterministic work over profiled examples does
  not regress.
