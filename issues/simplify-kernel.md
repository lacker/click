# Keep proof search out of kernel authority

## Status

This is a P1 architectural umbrella. Most of the original cleanup is complete:
the duplicate certification and evaluation routes, production environment
switches, dead fallbacks, general finite context splitting, contextual
canonicalization, global load-equality search, and the old fuel and structural
depth cuts have been removed. Smart loop closure, branch interfaces, resource
deltas, and quantified matching now retain checked local evidence.

The remaining work is to migrate the authoritative consumers of the general
proposition prover, listed below as work packages. The arithmetic migration is
a separate P1 implementation issue in [arithmetic.md](arithmetic.md), and
blocks completion of this umbrella.

Landed so far (2026-09-10): packages 1, 2, 3, 4, 5, 5b, 6, 7, 8, 9, 11
(first slice), 12, 13, 14, and 16, plus the package 0 census whose results are recorded below. Their sections remain as the record
of what was decided; each is marked landed.

This document is the complete brief for that work. An agent taking one work
package should be able to act from this file, the linked docs, and the code,
without the conversation that produced it. Line numbers are as of commit
`5c2ec4e8` and will drift; function names are the durable reference.

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

## What is being removed

The general prover is `PureFactContext::proves` in
`src/kernel/assumptions/proposition_reasoning.rs` (about line 188), with its
derivation-producing twin `derive_proposition` (about line 317) and the
premise-minimizing `atomic_derivation_premises` (about line 428). `proves` is a
recursive backtracking search over the goal's logical structure: it tries
facts, algebraic constructor rules, and the condition decision procedure, then
recurses through `And`, `Or` (arm choice), `Not`, `Implies` (clones the whole
context and assumes the antecedent), and `ForAll` (finite instantiation table or
binder dropping). When that fails it scans every condition fact for an
inconsistency and tries singleton substitution. `derive_proposition` adds case
splits over every disjunction fact, universal-instantiation search over all
`ForAll` facts, and pairwise candidate enumeration over loadability facts.

That logical search, and every authoritative kernel result that depends on it,
is what this issue removes. Non-test call sites under `src/kernel/` as of
`5c2ec4e8`: 95 `.proves(`, of which 34 are in `functions.rs`.

The atomic theory checkers underneath it are retained. See the next section.

## Boundary rulings

These rulings fix the scope of the umbrella. They were made to stop the
cleanup sprawling; each chooses the simplest option that does not prevent a
later, stricter migration. A work package must not reopen them. If a package
finds a ruling unworkable, it reports that with evidence and stops.

### Atomic theory checkers are retained, frozen

`PureFactContext::decide` in
`src/kernel/assumptions/condition_reasoning/decision.rs` (about line 239) and
the atomic memory and resource checkers (`proves_memory_loadable`,
`proves_memory_access`, `proves_memory_disjoint`, `proves_resource_separate`,
`proves_resource_contains`, and the memory-DAG and canonicalization equality
walks) are kernel theory checkers, not proof search. They decide one named
condition or atomic proposition by a fixed rule set over indexed facts and
return no derivation. They are out of scope for this umbrella and are governed
by [verification-efficiency.md](../docs/internals/verification-efficiency.md).

Three rules keep this from becoming the new sprawl:

1. **Freeze.** No new rules land in `decide` or the atomic checkers as part of
   this migration. A `proves` site may be converted to a `decide` or atomic
   call only when the proposition is already a bare `ConditionIs` or a bare
   atomic memory/resource proposition. That removes logical search without
   adding theory. Converting anything else is the "move proof construction to
   another kernel module" dodge and is forbidden.
2. **Efficiency debts are tracked separately.** `decide` still contains a few
   whole-context loops: the pointer-equality frontier loop in
   `condition_reasoning/order_paths.rs` (about line 472), the equality-edge
   loop there (about line 751), and the interval fallback in
   `condition_reasoning/overflow_intervals.rs` (about line 439). The order-fact
   collection in `condition_reasoning/bounds.rs` (about line 34) scans once per
   fact set and is memoized. These are indexing debts with scaling regressions
   as the remedy. They are not part of this issue and are not authorization to
   file one.
3. **Provenance stays.** `decide` records the premises it consumed through
   `record_implicit_reasoning_provenance`. That hook is the future path to an
   evidence-checked `decide`, following the existing `proves_exact` sibling
   pattern. Do not remove it.

One piece of `decide`'s support code is proposition-level derivation and is in
scope: `collect_derived_order_facts` in `condition_reasoning/bounds.rs` (about
line 60) walks every ambient proposition, discharges implication antecedents
by calling a prover (`proves_without_prop_facts`), and instantiates finite
universals to harvest order facts. See work package 13.

### Selections need a spelling; discharges become obligations

Every migrated consumer falls into one of two shapes.

A **discharge** asks "does this proposition hold here?" and, on success, drops
an obligation, prunes a path, or suppresses a fact. Discharges are migrated by
emitting the proposition as an explicit obligation on the execution path (the
existing `ProofObligation::verification_condition` route) and letting ordinary
Surface tactics prove it. No new evidence type is needed. The kernel may still
short-circuit a discharge with an exact test (`proves_exact`, an indexed fact
lookup, or a frozen atomic checker), never with `proves`.

A **selection** asks "which of these candidates applies?" and its answer
changes what is checked next: a disjunction arm, a covering segment, a
lexicographic pivot, a universal instantiation, a witness, a rewrite, a
contract branch. Selections over an open set already have Surface spellings
(`instantiate ... using`, `witness`, `choose`, `rewrite`, `transport ... using`).
Selections over a finite set that the kernel itself enumerates are migrated by
lowering the choice to an explicit finite disjunction obligation, so the
existing `left`/`right`/`cases` tactics make the choice and the expansion
prints it. Only when a finite disjunction would be unreasonably large may a
package propose a `using` clause on the consuming tactic; that proposal goes
to the user before implementation.

Consequence: this umbrella needs no new evidence vocabulary and no new proof
site in the language. Termination obligations join the existing back-edge
bundle (package 5). The only vocabulary decision left is the arithmetic
certificate form owned by [arithmetic.md](arithmetic.md).

### Retained evidence names premises, never a context

`PropositionDerivationRule::ContextualAtomic` and `Explosion` in
`src/kernel/primitives.rs` (about line 3774) embed a whole `PureFactContext`
as their "premises". Evidence that clones the context violates the efficiency
contract in the same breath that it satisfies the checking invariant. Any
evidence record created or retained by this migration names its premises as
exact propositions or indexed fact references. Package 15 replaces the two
context-embedding leaves.

### The prover moves out; it is not rewritten

At the end, the logical search in `proposition_reasoning.rs` is not deleted
outright. It becomes a Surface planner that advances state only through
checked operations, mirroring the direction [arithmetic.md](arithmetic.md)
sets for the arithmetic checker: the surface owns the algorithm and the kernel
checks its output. A package that needs planning logic in the surface may lift
the corresponding kernel code rather than reinventing it, provided the lifted
code no longer issues authority.

### Construction and verification check the same goal

Wherever a certificate is planned in one place and validated in another, both
sides must derive the goal by the same exact function. Planning may not use a
stronger prover than validation to decide what the goal is. Package 6 fixes
the known instance; any package that adds a certificate must share one goal
function between its planner and its checker.

### Lowering makes paths, not decisions

Where lowering currently decides a specification branch or omits an
obligation, it instead produces guarded paths and explicit obligations. The
paths mechanism already exists; this ruling forbids adding context-free
decisions to it. Packages 4 and 9.

### The certificate has no smart leaf

`ProofStep::CloseInvariants` is a smart step reachable inside a
`ProofCertificate` through `ProofCertificate::from_steps`, and automatic
loop-preservation planning appends `simp` to its generated body. Both
contradict the representation rule above. Package 14 closes them; until then,
no package may add another smart or internal-only step to `ProofStep`.

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
propositions. A fresh audit at `5c2ec4e8` found only five test callers
(`src/kernel/tests/execution_tests.rs`, `expression_tests.rs`,
`proof_reasoning_tests.rs`). Delete them.

After the named consumers are migrated, audit the remaining `proves` and
`derive_proposition` callers transitively. The audit stops at the atomic
theory boundary fixed above: `decide` and the atomic memory and resource
checkers are retained, not audited for search. A helper above that boundary
may remain only when its authoritative result is an exact, local rule over
named input. Merely wrapping the general prover or moving proof construction
to another kernel module does not complete the migration.

## Census results

Package 0 ran on 2026-09-10 at `34ef4d87`. It labeled 77 production prover
sites (95 grep hits minus test-only code, the prover's own recursion, and an
unrelated method of the same name), counted attempts and deciding successes
over both fixture harnesses, then reran with single sites denied. "Deciding"
means the general prover answered and none of the retained routes (builtin
solving, exact fact lookup, `decide` on a bare `ConditionIs`, the frozen
atomic checkers) would have. A denial run is stronger than the migration
because it also removes exact-covered answers; an "exact-only" run answers
from the retained routes only and is the true migration target. Believe the
exact-only number where both exist. The probe branch is
`claude/simplify-kernel-pkg-00-census`; it must never land.

Deciding successes by site, mdtests plus examples, all others zero:

| site | package | deciding | fixtures lost under the migration target |
|---|---|---|---|
| `bounds.rs::collect_derived_order_facts_from_proposition` | 13 | 249 | 1: `bubble_pass3_max_suffix` |
| `fact_reasoning.rs::normalizes_context_free` | 8 | 92 | 9: `bubble_pass3_max_suffix`, `bubble_sort3_loop_sorted`, `bubble_sort3_two_pass_sorted`, `copy3_array_demo`, `copy_n_segment_invariant`, `fill3_array_loop`, `fill_n_segment_invariant`, `fill_tail_old_prefix_segment`, `sort3_sorted` |
| `functions.rs::prepare_verified_function_call` (guarded requirement) | 10(c) | 40 | none |
| `loops.rs::condition_value_is_proven` | 4 | 32 | 2 (with `assume_invariant_checks`): `loop_quantified_memory_invariant`, `loop_sorted_range_invariant` |
| `termination.rs::ranking_proves` | 5 | 16 | 2: `c_decreases_resource_recursive_in_loop`, `_rejects_parent` |
| `api.rs::prove_universally_quantified_pure_implication` | 2 | 13 | none (landed) |
| `path_facts.rs::add_required_proof_obligation_with_context` | 4 | 12 | 2 exact-only: `bubble_sort3_two_pass_sorted`, `copy3_array_demo` (81 under full denial; 79 were exact-covered) |
| `loops.rs::assume_invariant_checks` | 4 | 8 | see `condition_value_is_proven` |
| `functions.rs::contract_refinement_proves` | 11 | 2 | none exact-only (15 under full denial) |
| `memory_reasoning.rs::pointer_access_in_range` | 16 | 2 | none |

Consequences for the packages:

- **26 sites are never reached by either harness**, including every package
  12 and 10(d) site, `assume_structural_path`, `capture_spec_algebraic_value`,
  all four `loop_effect_segment_contains_*` helpers, and the unreached arms of
  `contract_refinement_proves`. A package migrating one of these must first
  add a fixture that reaches it, or its regression proves nothing.
- **Packages 4, 8, and 13 collide on one fixture family** (the bubble-sort,
  copy, fill, and sort loop-invariant proofs). They share one owner and land
  in the order 4, 13, 8; do not run them in parallel worktrees.
- **Package 9 is nearly free and a measurable speedup.** `evaluate_spec_if_paths`
  runs the prover 41,503 times on an empty context for 11 successes, all
  exact-covered, and `assumptions_prove_proposition_false` 25,094 times for
  6.
- **Packages 10(c), 11, and 12 decide nothing the exact routes do not.** Their
  migration is a route restriction plus a fixture that would have needed the
  removed search.
- **Six prover calls sit inside the frozen boundary** and must go before
  package 15 can delete `proves`: two in `decide_algebraic_equality`
  (`condition_reasoning/decision.rs`, 1,074 attempts, 0 successes) and four
  in `pointer_access_in_range` (`assumptions/memory_reasoning.rs`, 291
  attempts, 2 deciding, denial breaks nothing). Package 16.

## Work packages

Each package is one coherent green change, or a short series of them, with
its own focused and scaling regressions. Packages list their entry points,
the choice the prover currently makes, the target design under the rulings
above, dependencies, and the regression that proves the package done.
Packages with no unmet dependency may run in parallel in separate worktrees.

### Package 0: temporary prover census

**Purpose.** Before any consumer migration with many callers, know which
`proves` sites actually decide anything in the fixture corpus.

**Target.** A thread-local census keyed by a static site label, counting
attempts and deciding successes (a success that no exact route already
covered), plus a denial switch per label that makes the site answer "no". Run
both fixture harnesses (`tests/mdtests.rs`, `tests/examples.rs`) with the
census on, then with each interesting label denied. A fixture that passes with
a route denied did not need it.

**Constraints.** The census and switches are probes: they live on the task
branch only and must not land. The existing body-rerun census in
`src/instrumentation.rs` (`ContractFallback`) is a model for shape but counts
something else; do not reuse its counters. Record results in the package
report, not in the tree.

**Dependencies.** None. Packages 4, 10, 11 require its results.

### Package 1: delete legacy theorem constructors

**Landed** 2026-09-10 ("Delete legacy theorem constructors that re-prove added propositions").

**Entry points.** `src/kernel/api.rs::prove_c_function_satisfies_specification_and_propositions`
(about line 4078) and `prove_c_statement_executes_and_propositions` (about
line 4122). Both call `proves` on every added proposition.

**Target.** Delete both, their tests, and any `pub use` that exported them.

**Regression.** The gate. No new test.

**Dependencies.** None.

### Package 2: retain pure-theorem completions

**Landed** 2026-09-10 ("Issue pure-theorem authority from the retained proof completion"). The completion is `CheckedProposition` carrying the root `ProofFacts` it was closed under; both constructors are `pub(crate)` and take it. Known narrowing: a pure theorem whose certificate uses `instantiate` is not checked by the proof object today, so it now publishes no whole-contract certification authority. The corpus has one such theorem (`bounded_value` in `mdtests/pure_theorem_instantiate.md`) and nothing consumes its authority. Restoring it belongs to the legacy pure-driver migration, not this umbrella.

**Entry points.** `src/kernel/api.rs::prove_universally_quantified_pure_implication`
(about line 4639) and `_by_int32_rewrites` (about line 5096). Sole non-test
caller: `src/surface/proof/pure_theorems.rs` (about lines 1434 and 1461),
which has already checked a full certificate through
`pure_goal_proof_certificate_gateway`.

**Choice made today.** The whole proof of the conclusion from the
requirements, re-proved from scratch; in the rewrite variant, each rewrite
equality is re-proved from the requirements and the rewritten goal is closed
by `proves` on the empty context.

**Target.** The constructor accepts the checked completion and validates
exactly: the requirement set, the declared variable set equals the free
variables, the rewrite list and orientation (`rewrite_int32_term_by_exact_equality`
stays), the conclusion identity, and that the completion's goal is the
conclusion. No `proves` call remains. The rewrite variant cites each rewrite as
an exact available equality, not a proved one; if a fixture relied on a
derived rewrite, the surface proof spells the derivation.

**Regression.** Tamper tests: a completion for a different conclusion, a
missing requirement, a reordered rewrite, and a rewrite not among the
requirements are each rejected.

**Dependencies.** None.

### Package 3: exact quantity and resource-algebra rules

**Landed** 2026-09-10 ("Decide quantity and separation by exact routes, not the general prover" and its scaling regressions). All eight helpers share `resource_algebra.rs::quantity_condition_holds`: `proves_exact`, then `decide` on the bare condition. The `decide` leg is load-bearing (`examples/binary-tree` fails without it). No fixture changed and nothing needed package 4.

**Entry points.**
`src/kernel/functions.rs::population_quantity_is_zero`, `_is_positive`,
`population_quantities_are_equal` (about lines 7522 to 7547);
`src/kernel/primitives/resource_algebra.rs::resource_quantity_at_least`
(about line 2210), `resource_quantity_is_positive` (about line 2225),
`consume_exact_resource_fact` (about line 2262),
`CResourceFact::core_with_assumptions` (about line 3244),
`is_proven_separate_from_allocation_with_element_width` (about line 3193).

**Choice made today.** Whether a quantity relation or separation holds, found
by `proves`.

**Target.** Follow `resource_quantity_is_zero` (about line 2249), which already
uses `proves_exact`. Each helper becomes an exact lookup or a frozen atomic
checker call. Where a fixture then fails, the relation becomes an explicit
obligation (discharge shape) rather than a broader kernel rule.

**Regression.** Multi-size scaling test: quantity checks with growing
unrelated fact context show flat work. Existing resource fixtures pass.

**Dependencies.** None. Do this before package 10 so the population code has
exact primitives to call.

### Package 4: obligation propagation in lowering and execution

**Landed** 2026-09-10 (two commits, "cf4c05e2"/"cc097207" on the loop-family
branch). Every listed site is a route restriction: `proves_exact`, the
frozen condition checker on a bare `ConditionIs` (`condition_is_decided`,
`bare_condition_is_decided`), or the new
`PureFactContext::proves_atomic_memory_or_resource` dispatch over the five
retained atomic arms, which a corpus census showed is exactly what the
obligation route ever decided (517 loadability and 4 store obligations,
nothing else). Deviation: the two `loop_effect_segment_contains_*` helpers
became `decide` on their bare conditions rather than two ordered
obligations, sanctioned by the freeze rule and preserving six diagnostics
fixtures; the census listed them as never reached. Structural change:
restricting the required-obligation route exposed that
`c_loop_invariants_hold_at_entry` re-lowered invariants from the
post-initialization facts while planning used the entry obligations, so
`verify_loop_initialization_pure_proof` now checks the obligations it was
given through `loop_entry_checked_goal` plus an exact walk down each
goal's leading-implication chain. No fixture proof text changed.

**Entry points.**
`src/kernel/reasoning/path_facts.rs::add_path_fact_with_visibility_after_effect`
(about line 604; drops a fact when `proves` says it is redundant),
`add_condition_path_fact_with_visibility` (about line 653; `decide` may
reject the path), `add_proof_obligation_with_context` (about line 748) and
`add_required_proof_obligation_with_context` (about line 777; both suppress
an obligation when `proves` succeeds), `add_condition_obligation` (about line
865), `decide_with_facts` (about line 1022);
`src/kernel/spec.rs::capture_spec_algebraic_value` (about line 36; hard error
on an unproved evaluation obligation),
`evaluate_spec_expression_paths_with_algebraic_bindings` (about line 3083;
overflow obligation pushed only when `proves` fails),
`lower_spec_sequence_membership_at_state` (about line 1262; membership decided
by scanning members);
`src/kernel/loops.rs::condition_value_is_proven` (about line 1271),
`loop_effect_segment_contains_pointer` and `_contains_range` (about lines
2601 and 2620), `assume_invariant_checks` (about line 2673).

**Choice made today.** Whether to emit, suppress, or discharge each obligation
and fact.

**Target.** Redundant-fact suppression uses `proves_exact` or is deleted.
Obligation suppression uses `proves_exact` or a frozen atomic checker; every
other case emits the obligation. `add_required_proof_obligation_without_search`
(about line 799) is the already-migrated sibling to copy. Segment containment
in `loops.rs` becomes two ordered obligations. Sequence membership becomes a
finite disjunction obligation over members (selection shape). `decide` calls
that reject a path stay, under the freeze rule, because `decide` is a retained
checker; `proves` calls that reject a path do not.

**Expected cost (measured).** The census puts this package's whole cost in
four fixtures: `add_required_proof_obligation_with_context` under exact-only
loses `bubble_sort3_two_pass_sorted` and `copy3_array_demo`;
`condition_value_is_proven` together with `assume_invariant_checks` loses
`loop_quantified_memory_invariant` and `loop_sorted_range_invariant`. Every
other listed site either never fires or is fully exact-covered, so migrating
it is a route restriction. Those four fixtures are the same family package 8
breaks; this package owns them first, then 13, then 8. Measure deterministic
work on profiled examples before and after and report the delta.

**Regression.** For each suppressed obligation class, a fixture where the
obligation is unprovable must now fail at that obligation with a prompt
diagnostic rather than pass silently. Scaling test: obligation emission is
flat in unrelated context size.

**Dependencies.** Package 0 results.

### Package 5: termination evidence

**Landed** 2026-09-10 (three commits, "Move loop ranking obligations into
the close_invariants bundle" onward). `CStatement::While` carries
`ranking_measures`; `loops.rs::collect_loop_ranking_obligations` appends,
after the invariants, one nonnegativity member per component then one
decrease member (right-nested pivot disjunction for tuples), at both the
surface `close_invariants` route and the kernel-executed preservation
route; `CheckedLoopInvariantLowerings` compares the measures exactly.
`ranking_proves`, the pivot loop, the opportunistic strengthening, and the
whole separate ranking context (about 580 lines of termination.rs) are
deleted; `check_loops` only binds a verified rule's measure by index and
shape. Expansion of the lexicographic fixture prints `right();` on the
path where only the second component decreases and `left();` on the other,
and swapped arms are rejected. Deviations and follow-ups:

- `assume_structural_path` is route-restricted to `proves_exact`, not
  emitting, because it is a boolean helper inside witness-child comparison
  with no proof site to receive an obligation; refusing the path is the
  conservative equivalent. No reaching fixture exists; a kernel unit test
  pins the route.
- **Package 5b, landed** 2026-09-10 ("Close loop ranking members from the
  smart invariant-bundle closer"). When the closer body is exactly the
  single `simp` (bare `close_invariants()`, the omitted body, or the region
  `simp()`), a planner in `execution_statements.rs` descends the bundle's
  own structure through checked operations: `both` over `And`, `left`/`right`
  over the pivot `Or`, and one `arithmetic() using` per member citing a
  named premise set: each declared invariant as written and at iteration
  entry, the guard at iteration entry, and the function's `requires`
  conjuncts, each kept only if exactly available and accepted by the affine
  checker. No ambient scan; a regression drops an invariant and shows the
  same inequality left ambient is not found. Seven fixtures are back to
  bare closers; `c_decreases_loop` and `c_decreases_rejects_bad_loop_path`
  keep explicit bodies as hand-written coverage. Deterministic work rose
  30 to 55 percent on the restored fixtures, which is the planning the
  source no longer spells, far under budget. Limit: the planner is gated
  on the `[simp]` body; a hand-written `both { simp(); } and { simp(); }`
  does not get the arithmetic candidate at its leaves.
- The failure diagnostic names all of a loop's ranking members rather than
  the one left open; pinpointing would rerun the closer per member.
- Hand-written ranking premises spell iteration entry as
  `at(statement(N).entry, x)`, existing grammar but brittle under source
  edits; a friendlier selector would be a language addition.
- Deterministic work fell about 5% on the explicit fixtures and rose about
  10% on the lexicographic one, whose pivot is now found by the region
  `simp()` planner.

**Entry points.** `src/kernel/termination.rs::assume_structural_path` (about
line 508; discharges non-loadability path obligations with `decide`/`proves`),
`ranking_proves` (about line 2111; `proves`, then the affine checker over the
entire condition-fact set), `ranking_proves_lexicographic_decrease` (about
line 2124; tries every pivot index, assuming the equality prefix unproved),
and the caller block in `check_loops` (about lines 2405 to 2455), which runs
as a separate kernel pass over each back-edge path with its own ranking
context and no surface proof site. The back-edge bundle it will join is
built by `src/kernel/loops.rs::collect_invariant_check_obligations_with_mode`
(about line 1643) and consumed by `Proof::apply_close_invariants_body` and
`certify_loop_invariant_bundle` in
`src/surface/proof/proof_object/execution_statements.rs`.

**Choice made today.** The pivot; the premises for the affine checker; the
discharge of each structural-path obligation.

**Target (decided).** Loop ranking obligations join the `close_invariants`
bundle at the back edge. When a loop declares `decreases`, the bundle gains,
in this fixed order after the invariants in declaration order: one
nonnegativity obligation `0 <= component` per ranking component, evaluated
at the back edge; then one decrease obligation. For a single component the
decrease obligation is `post < pre`. For a tuple it is the right-nested
finite disjunction over pivots
`(post[0] < pre[0]) or ((post[0] == pre[0]) and (post[1] < pre[1])) or ...`,
where `pre` is the component value at preserve entry and `post` its value at
the back edge. The pivot is then the arm choice a proof makes with `right`
and `left`, and expansion prints it. `close_invariants()` closes the ranking
members by the same smart planning it uses for invariants;
`close_invariants by { ... }` spells them with `both` and arm tactics. The
whole-function termination certificate consumes the retained bundle checks
for that loop; `check_loops` no longer proves anything. `ranking_proves`, the
pivot loop, and the opportunistic context strengthening at about lines 2416
to 2423 are deleted. The existing ranking-context rules (loop guard,
invariants, path conditions, exclusion of addressed and pointer variables,
nested-loop forgetting) become facts available to the bundle proof, not a
separate prover context. Structural-path obligations in
`assume_structural_path` are emitted as obligations, not discharged.

Function-level `decreases n` on recursive C functions needs no proof site:
its obligation arises at each recursive call and is emitted as a call
obligation under package 10(c), like a precondition.

**Language.** No grammar change. Bundle membership order must be
deterministic so retained certificates are stable across runs and sites. An
explicit `preserve by` body written before a `decreases` clause was added
must fail promptly with a diagnostic naming the unproved ranking member; a
smart body absorbs the new members and expansion prints them. Update the
`close_invariants` rows in `docs/reference/tactics/index.md` and the
termination section of `docs/reference/language/index.md` to say that
ranking obligations are back-edge bundle members. A separate `decrease by`
phase may be added later as sugar that routes into the same bundle; it is not
part of this package.

**Regression.** The lexicographic fixture
`mdtests/c_decreases_lexicographic_loop.md`, whose only valid pivot on one
path is the second component: expansion prints the arm choice inside the
`close_invariants by` body, and a certificate with the other arm, a missing
nonnegativity member, or a reordered member is rejected. A loop whose
component can go negative on one back edge fails at that member with the
member named. A scaling test with growing unrelated inequalities in scope
shows flat work for the bundle check, since arithmetic premises are the
cited ones only.

**Census.** `ranking_proves` decides 16 times in mdtests; denying it loses
only `c_decreases_resource_recursive_in_loop` and its `_rejects_parent`
sibling, so those two are the fixtures to watch. `assume_structural_path`'s
non-loadability arm is never reached by either harness; add a fixture that
reaches it before claiming it migrated.

**Dependencies.** Package 4 (obligation emission shape) and package 14
(landed: the bundle step is `CloseInvariantsBy` with an expanded body, so
the printed pivot cannot hide behind a smart leaf). Arithmetic obligations are
closed by `arithmetic() using`, so this package does not depend on
[arithmetic.md](arithmetic.md).

### Package 6: one goal for loop-entry planning and validation

**Landed** 2026-09-10 ("Share one goal between loop-entry planning and validation"). `loop_planning.rs::loop_entry_checked_goal` is the shared function. No fixture's expansion changed: the retained certificates already carried the introductions, so the defect was goal-versus-fact identity, not a missing step. The helper `invariant_lowering_under_guards` mirrors the `intro` shape heuristic and is package 7's to replace with provenance.

**Entry points.** `src/surface/proof/execution_planning/loop_planning.rs`:
planning strips leading implications with `planning_assumptions.proves`
(about line 121) and separately with exact containment (about line 129);
validation strips with exact containment only (about line 294).

**Choice made today.** Which leading antecedents of the entry obligation are
already known, decided by a stronger prover during planning than during
validation.

**Target.** One shared function computes the checked goal from the exact
obligation and the exactly available facts. Planning uses it and, where an
antecedent is not exactly available, emits an `intro` plus a proof of the
antecedent into the certificate so the retained certificate discharges the
complete obligation. Validation uses the same function. The `proves` call is
deleted.

**Regression.** A loop whose entry obligation has a leading guard that is
derivable but not exactly present: the expansion contains the explicit
introduction, and deleting it from the certificate is rejected at validation.

**Dependencies.** None, but package 7 makes the `intro` targeting exact; land
6 first with the current heuristic and note the dependency in the report.

### Package 7: lowering provenance for hidden guards and binders

**Landed** 2026-09-10 (four commits, "Record lowering provenance for hidden
guards and binders" through "Regress the retained antecedent against a
refuted re-lowering"). The record is `LoweringIntroductions` in
`path_facts.rs`: a linear head chain of the lowered proposition, outermost
first, one entry per introducible node (`PathFactGuard`, `ObligationGuard`,
`WrittenImplication`, `WrittenNegation`, `WrittenUniversal`). The kernel
`Proposition` is unchanged; `SpecPropositionPath` carries the chain and
`c_lower_spec_proposition_at_state_with_provenance` returns it. All three
prerequisite bullets are done for goals that lowering produced; `intro`,
`extract`, `contradiction`, `arithmetic using`, `normalize using`, and
pure-proof lowering consult the retained binding. Two limits remain, both
other packages' territory: kernel-built obligations from calls and loop
bundles (`functions.rs`, `loops.rs`) carry no chain and fall back to
structural refinement of the written form (packages 4 and 10), and
`plan_context_free_normalization_with_assumptions` still pairs by shape
below the recorded chain (package 8). The `invariant_lowering_under_guards`
replacement was not done; package 8's owner does it while migrating the
planner.

**Entry points.** `src/kernel/reasoning/path_facts.rs::wrap_path_context`
(about line 72; folds path obligations and facts into kernel `Implies` nodes
with no Surface connective) and `wrap_proof_facts` (about line 29); the
callers in `spec.rs` (about lines 369 to 425) and `functions.rs` (about lines
1540 to 4715); the `intro` heuristic in
`src/surface/proof/proof_object/step_application.rs` (about lines 303 to 322),
which guesses whether an implication is written or a lowering guard;
`SurfacePropositionMap` in `src/surface.rs` (about line 891), which links
whole propositions only.

**Choice made today.** None by the prover; this is the prerequisite the
quantifier prototype failed on.

**Target.** Lowering output carries, per inserted `Implies` node and per
quantifier binder, a provenance record: which lowering step inserted it
(obligation guard, path fact guard, written connective) and the exact binder
substitution. `intro` consults that record instead of the heuristic; `extract`,
arithmetic premise lowering, and contradiction citations consult the retained
binding. Introducing an implication retains the checked Surface-to-kernel
antecedent pair and its structural subfacts at introduction time.

**Regression.** A goal with a hidden loadability guard in front of a written
implication: `intro` introduces the guard without unfocusing the written goal,
and a second `intro` introduces the written antecedent; expansion prints both
in order and reordering is rejected. A universal whose binder appears in a
later `extract` argument resolves through the retained binding.

**Also owned here.** `loop_planning.rs::invariant_lowering_under_guards`,
landed by package 6, decides written-versus-guard by Surface constructor
shape. Replace that with the provenance record as part of this package.

**Dependencies.** None. Blocks packages 8 and 9.

### Package 8: quantifier normalization

**Landed** 2026-09-10 ("b0399e6b"). `normalizes_context_free_leaf` rejects
`ForAll` and `Exists`; the planner spells `intro` and recurses into the
written body; a vacuous universal gets an explicit `enumerate` with zero
instances; `apply_enumerate` and `ProofFacts::contradicts` no longer call
`derive_proposition`. Fixture proof text changed, C and claims unchanged:
`copy3_array_demo` and `bubble_sort3_two_pass_sorted` (vacuous entry
invariants, `normalize()` to `enumerate()`), `loop_entry_guard_intro`
(same), `exists_and_symbolic_any` and `pure_click_functions` (concrete
range `any` goals now name `witness(k = 1)`). Deterministic work fell 23
to 27 percent on the copy and bubble fixtures. Non-test `.proves(` sites
under `src/kernel/` are now 55. Left for package 17:
`invariant_lowering_under_guards` and the planner's written-body pairing
still decide by Surface constructor shape because loop-bundle obligations
carry no provenance chain.

**Entry points.** `src/kernel/proof/fact_reasoning.rs::normalizes_context_free`
(about line 984), `normalizes_context_free_leaf` (about line 995),
`normalize_using_conditions` (about line 1010); the other callers of the
non-leaf version in `src/kernel/proof/object.rs::apply_enumerate` (about
lines 802 and 810) and `src/kernel/proof/facts.rs::ProofFacts::contradicts`
(about line 402); the surface planner
`src/surface/proof/surface_certificates.rs::plan_context_free_normalization_with_assumptions`
(about line 68), which already spells `both`, `left`/`right`, and `intro` for
top-level connectives.

**Choice made today.** `derive_forall_rule` chooses among binder dropping,
loadable-range derivation (which selects a source loadability fact), the
finite instantiation table, and an atomic leaf; existential witness versus
fact versus loadable range; nested connectives under a quantifier; universal
instantiation for atomic leaves.

**Target.** The leaf rejects `ForAll` and `Exists`. The surface planner spells
`intro` for universals, `witness`/`choose` for existentials, `enumerate` for
finite instantiation, `instantiate ... using` for cited instantiations, and
recurses into the body with the existing connective planning. The cases listed
under "Quantifier migration prerequisites" are the minimum fixture set. The
`apply_enumerate` and `contradicts` callers move to the leaf or to explicit
steps.

**Regression.** The five cases listed above, each with: smart verification,
expansion inspection, independent verification of the expansion, and rejection
of a deleted or reordered introduction.

**Census.** `normalizes_context_free` is genuinely load-bearing: denying its
`derive_proposition` leg (the atomic leg is already tried first) fails nine
fixtures, all in the bubble-sort, copy, fill, and sort loop-invariant family.
Those proofs need explicit quantifier steps. This package runs after 4 and
13 under the same owner.

**Dependencies.** Packages 6 and 7, and packages 4 and 13 for fixture
ownership.

### Package 9: specification branch selection during lowering

**Landed** 2026-09-10 (three commits, "Decide a specification if by exact
constant folding only" through "Pin the specification-conditional lowering
boundary"), with one deliberate deviation from the target below. Both
prover sites now route through `constant_spec_condition_value`: builtin
solving, builtin disproof, then `decide_intrinsically` on a bare condition;
no ambient fact is read, and `assumptions_prove_proposition_false` is
deleted. An undecided condition lowers, as before, to the total
if-then-else term covering both branches with both branches' obligations
emitted. The guarded-two-path lowering was implemented, measured, and
reverted: `c_lower_spec_proposition_at_state_with_provenance`,
`c_evaluate_spec_expression_at_state`, and range-fold body lowering all
require exactly one path, and the prelude's `list_contains` and `count`
use specification conditionals, so every fixture failed. Making that
target real means making pure-theorem, contract-clause, and fold-body
lowering path-aware, a separate package if ever wanted; the boundary ruling
is satisfied without it. The whole-context fallbacks that every failed
empty-context `proves` ran (`proposition proof: context inconsistency` and
`singleton substitution`, 999 calls on `sort3_permutation`) no longer
appear in profiles. Also fixed in passing, pre-existing: expansion rendered
a specification `if` as `if c then a else b`, which no parser accepts; it
now prints `(if c { a } else { b })`. Known weaker spot, unreached by the
corpus and predating this package: `conditional_spec_value` returns `None`
when the two branch values are not both `Int32`, silently dropping the
path.

**Entry points.** `src/kernel/spec.rs::evaluate_spec_if_paths` (about line
3892; decides a spec `if` condition with `proves` on an empty context, about
line 3920) and `assumptions_prove_proposition_false` (about line 4299).

**Choice made today.** Which branch of a specification conditional is lowered.

**Target.** Lower both branches as guarded paths, with the condition and its
negation as path facts. Exact constant folding of a literally constant
condition stays. Proof-time tactics (`if`, `cases`) choose the branch. This is
the same shape as C branches.

**Regression.** A specification `if` whose condition is provable only from
ambient facts: verification requires an explicit branch step; expansion prints
it. Multi-size scaling on the number of ambient facts is flat.

**Census.** The two sites run the prover 66,597 times on an empty context
for 17 successes, all exact-covered. Migration loses no fixture and should
show as a deterministic-work drop on profiled examples; report it.

**Dependencies.** Package 7 (guard provenance), package 4 (path obligation
shape).

### Package 10: calls and resource populations

**Entry points.** In `src/kernel/functions.rs`:
`prepare_verified_function_call` (about line 1419; precondition discharge at
about lines 1547 and 1606, with exact routes already tried first at about
lines 1563 to 1585), `evaluate_decided_contract_mutable_ranges` (about line
2375), `mutable_footprint_is_compatible` (about line 2713; selects the
covering segment by trying each), `lower_refinement_mutable_guards` (about
line 2793), `assume_contract_proposition` (about line 3019),
`prove_contract_propositions` (about line 3044),
`add_verified_function_ensure_facts_selected` (about line 4572; strips ensure
premises while `proves` succeeds), `allocation_continuity` (about line 4729),
`prepare_function_resource_transfer` (about line 7102),
`apply_counted_population_transitions` (about line 7694; each miss already
falls through to a verification condition), `held_child_witness` (about line
8266), `rewrite_resource_instance_selecting_children` (about line 8376),
`evaluate_guarded_contract_condition` (about line 9021; only the final
`|| assumptions.proves(proposition)` leg is non-exact),
`evaluate_resource_population_fact_propositions` (about line 9354),
`evaluate_composite_resource_fact_propositions` (about line 9773),
`evaluate_function_resource_spec` (about line 10258).

**Choice made today.** Whether each precondition, guard, transition, and
resource fact is discharged; which mutable segment covers; how many ensure
premises are stripped.

**Target.** Split into slices by evidence type, in this order, each landing
green: (a) quantity and population transitions, using package 3 primitives
and the existing verification-condition fallthrough; (b) contract condition
and guard evaluation, dropping the `proves` leg so the answer is
true/false/undecided by exact and frozen routes only, with undecided becoming
an obligation; (c) precondition discharge, which emits an obligation per
requirement path when the exact routes fail, and the function-level
`decreases` obligation at each recursive call (package 5 decided that this
is a call obligation, not a proof site); (d) covering-segment selection as
a finite disjunction obligation over the callee's declared segments; (e)
ensure-premise stripping, which retains the list of stripped premises and
requires each to be exactly available or emits it.

**Regression.** Per slice: a fixture where the discharged condition is false
must fail at the obligation; expansion of a smart proof shows the discharging
steps; scaling in unrelated context is flat.

**Census.** Slice (c)'s guarded-requirement site decides 40 times but denying
it loses nothing; slice (d)'s sites and several others (`allocation_continuity`,
`assume_contract_proposition`, `prove_contract_propositions`,
`lower_refinement_mutable_guards`, `evaluate_decided_contract_mutable_ranges`,
`evaluate_guarded_contract_condition`) are never reached by either harness,
so each needs a reaching fixture before its migration counts. Also in this
package: `ResourceContext::satisfies_fact`'s miss path scans unrelated
ambient condition facts linearly (measured 40 to 264 work over sizes 16 to
128 after package 3); it belongs to the resource slice.

**Dependencies.** Packages 3 and 4. Slice (c) benefits from package 7 because
requirement obligations are path-guarded.

### Package 11: contract refinement

**First slice landed** 2026-09-10 ("Decide contract refinement clauses by
exact routes only"). All four `proves` calls route through
`refinement_route_proves`: `proves_exact`, then `decide` on a bare
`ConditionIs` or its negation. The antecedent-assumption clone is deleted;
an `Implies` clause holds when its antecedent is exactly refuted or its
consequent holds alone. Four fixtures now reach the previously unreached
arms. Findings: `decide` proves `x < x + 1` but not `x + 1 > x`, an
orientation gap in the frozen checker worth knowing before packages 10(b)
and 13; `assume_contract_proposition` and `prove_contract_propositions`
still call `proves` and belong to package 10; `recorded_equality_class`
builds its memoized index by one scan of condition facts per context, an
indexing debt under the efficiency contract. The second slice below is
still open.

**Entry point.** `src/kernel/functions.rs::contract_refinement_proves` (about
line 3088). A second hand-rolled prover: sequence-elementwise descent, `Or`
arm choice, `And`, `Implies` with antecedent assumption, then a search over
`recorded_equality_class` rewrites of both sides.

**Choice made today.** Sequence index alignment, arm, equality-class
representative.

**Target.** Refinement becomes an ordinary obligation whose proposition is the
refinement implication, proved by existing tactics (`both`, `left`/`right`,
`intro`, `rewrite`). The kernel keeps only the exact structural check that the
two contracts have compatible shape. If the census shows the equality-class
search decides real fixtures, spell those as `rewrite` steps in the affected
proofs.

**Regression.** A refinement that holds only under an equality rewrite: the
proof must cite it; expansion prints it; the certificate without it is
rejected.

**Census.** Restricting the head site to exact routes loses no fixture, and
the equality-class rewrite site's ten successes are all exact-covered; two
arms are never reached. So the first slice is a route restriction plus a
fixture that reaches each arm; the obligation form above is the second
slice.

**Dependencies.** Packages 4, 10(b).

### Package 12: loop-rule prerequisite selection

**Landed** 2026-09-10 ("Select verified loop rules by exact prerequisites
only"). The `proves` leg and the `pure_facts().contains` materialization are
gone; each required assumption must be `proves_exact`-available. A probe
over the whole mdtest corpus showed the site is a discharge, not a
selection: `CLoopInvariantCheck` labels make every source loop a distinct
statement, so `(entry state, loop statement)` already keys exactly one
rule, and no disjunction lowering or `using` clause is warranted. Scaling
regression: 155/299/587/1163 work before, 0 at every size after. Left
undone with reason: an end-to-end fixture where a rule is rejected for a
missing prerequisite needs one source loop planned on two proof paths, and
a `loop` tactic inside a `branch` arm is rejected today (the arm's
interface trace names the pre-binding source while the loop tactic rebinds
it), a goal-identity gap in package 7's family; the kernel unit tests cover
the rejection instead.

**Entry point.** `src/kernel/primitives/contracts.rs::applicable_verified_loop_rule`
(about line 1683). Selects a verified loop rule by iterating all rules and
asking `proves` whether each rule's required assumptions hold.

**Target.** The consuming step names the rule; each required assumption is
exactly available or is emitted as an obligation. If no surface form names the
rule today, the selection is lowered as a finite disjunction over candidate
rules (selection shape) before proposing syntax.

**Census.** Never reached by either harness (6 attempts, 0 successes). The
regression below is also the first fixture to exercise the site.

**Regression.** Two applicable rules with different prerequisites: the proof
names one; the other is rejected without its prerequisite.

**Dependencies.** Package 4.

### Package 13: derived order facts

**Landed** 2026-09-10 ("4d4fc3b6"). `proves_condition_from_derived_order_facts`
reads `condition_order_facts()` only; the whole-`prop_facts` walk and the
in-query quantifier instantiation are gone, and `proves_without_prop_facts`
no longer appears in `bounds.rs`. The residual structural walk, reachable
only from the simplifier's named quantified instantiation, consumes guards
by structural conjunction split and exact or `decide` leaves.
`bubble_pass3_max_suffix` survived the exact-only target. No fixture text
changed.

**Entry point.** `src/kernel/assumptions/condition_reasoning/bounds.rs::collect_derived_order_facts`
(about line 60), which walks all `prop_facts`, discharges `Implies`
antecedents through `proves_without_prop_facts`, and instantiates finite
universals.

**Target.** The theory reads order facts only from `condition_facts`. Order
facts that live inside conjunctions, guarded implications, or finite
universals reach `condition_facts` through explicit `extract`, `intro`, and
`enumerate` steps, or through an exact structural fact-splitting rule at
assumption time that has no prover call. The `proves_without_prop_facts` call
is deleted.

**Regression.** A bound that is only available under a guarded implication:
proof requires the explicit step; scaling in the number of unrelated
propositions is flat.

**Census.** 249 deciding successes, the largest in the tree, but denying the
site loses only `bubble_pass3_max_suffix`. Same fixture family as packages 4
and 8; same owner, lands between them.

**Dependencies.** Package 4 for fixture ownership.

### Package 14: no smart leaf in the certificate

**Landed** 2026-09-10 ("Keep smart leaves out of proof certificates"). Parts (a) and (b) landed as specified: the `CloseInvariants` step variant is deleted, `from_steps` validates through an exhaustive step classifier, and expansion output is byte-identical on the loop fixtures. Part (c) was a false premise: the `simp` appended by automatic preservation planning only drives per-invariant preplanning and never becomes a retained step, because the retained closer is already gated by the smart-rejecting validator. A regression pins that. Do not replace that `simp` with `close_invariants()`; it would drop the preplanning.

**Entry points.** `ProofStep::CloseInvariants` in `src/surface.rs` (about line
2742), produced by `Proof::certify_loop_invariant_bundle` in
`src/surface/proof/proof_object/execution_statements.rs` (about line 387);
`ProofCertificate::from_steps` (about `src/surface.rs` line 2765), which
skips the smart-step rejection that `from_proof_tactics` performs; the
appended `ProofTactic::Simp` in
`src/surface/proof/execution_planning/forward_planning.rs` (about line 203).

**Target.** The bundle step is `CloseInvariantsBy(certificate)` with the
expanded body; `from_steps` validates like `from_proof_tactics`. (The third
target originally listed here, expanding the appended `simp`, was withdrawn;
see the landed note above.)

**Regression.** Expanding any loop fixture yields a certificate that
`from_proof_tactics` accepts; a certificate containing `close_invariants()`
is rejected by `from_steps`.

**Dependencies.** None.

### Package 15: relocate the prover and delete authority

**Entry points.** `PureFactContext::proves`, `derive_proposition`,
`atomic_derivation_premises`, `select_forall_int32_instantiation_evidence`,
`derive_by_singleton_substitution`, `derive_by_disjunction_cases`,
`is_inconsistent` as used from `proves`, and the context-embedding leaves
`ContextualAtomic` and `Explosion`.

**Target.** After packages 1 to 13, no authoritative kernel result calls
`proves` or `derive_proposition`. Move the logical search to a surface planner
module that advances state only through checked operations, delete the kernel
entry points, and replace the two context-embedding evidence leaves with
premise-naming records. The atomic checkers named in the boundary rulings
remain in the kernel unchanged.

**Regression.** A grep for `.proves(` and `derive_proposition(` under
`src/kernel/` outside tests is empty; every fixture harness passes; profiled
deterministic work does not regress.

**Dependencies.** All other packages and [arithmetic.md](arithmetic.md).

### Package 16: delete prover calls inside the frozen checkers

**Landed** 2026-09-10 ("Delete prover calls inside the frozen atomic
checkers" and its test repin). All six calls deleted, none kept. Sound
completeness narrowing: `decide` no longer bridges an algebraic `Equal`
premise to its condition form or sees distinct constructors in the condition
form; only two synthetic unit tests exercised that, and they now pin the
exact route. A local closure named `proves` in `memory_reasoning.rs` remains
and is exact.

**Entry points.** `src/kernel/assumptions/condition_reasoning/decision.rs::decide_algebraic_equality`
(two `proves` calls near the top of the file) and
`src/kernel/assumptions/memory_reasoning.rs::pointer_access_in_range` (four
`proves` calls, about lines 1637 to 1660).

**Census.** 1,074 attempts and 0 successes for the first; 291 attempts, 2
deciding successes for the second; denying both breaks nothing.

**Target.** Delete the calls. The freeze rule permits deletions from the
frozen checkers and nothing else. Where a call had an exact sibling route,
keep the sibling; add none.

**Regression.** The gate. If a deletion loses a fixture, that fixture is the
regression and the deletion becomes an explicit obligation instead.

**Dependencies.** None. Blocks package 15.

### Package 17: provenance on kernel-built obligations

**Entry points.** `ProofObligation` (src/kernel/assumptions.rs), the loop
bundle collection `loops.rs::collect_invariant_check_obligations_with_mode`
and `collect_loop_ranking_obligations`, the call-requirement obligations in
`functions.rs::prepare_verified_function_call`, and their consumers
`loop_planning.rs::invariant_lowering_under_guards` and
`surface_certificates.rs::written_universal_body`.

**Why.** Package 7 attaches a `LoweringIntroductions` chain only to goals
that lowering produced. Obligations the kernel builds itself (loop bundle
members, call requirements) carry none, so two surface helpers still pair
the written proposition with its kernel form by constructor shape. That is
goal-presentation fidelity, not proof search; no authority depends on it.

**Target.** `ProofObligation` carries the chain; the two collectors fill it
from `wrap_path_context_with_introductions`; the two consumers read it and
the shape heuristics are deleted. `intro` on a loop-bundle member targets a
hidden guard exactly as it does on a lowered goal.

**Regression.** A loop invariant whose lowering inserts a loadability guard
in front of a written implication: the retained certificate introduces
both in order, and reordering is rejected; the same certificate checks at
planning, validation, and the entry check.

**Dependencies.** None. Not blocking 15.

### Dependency order

Landed: 0, 1, 2, 3, 4, 5, 5b, 6, 7, 8, 9, 11 first slice, 12, 13, 14, 16.
Open: 10 (slices a to e), 11 second slice after 10(b), 17, then 15 last.
After 4: 12, 5, 10(a), 10(b). After 7 and 4: 9. After 10(b): 10(c), 10(d),
10(e), 11 second slice. Last: 15.

Rough size after the census, for scheduling only: small = 16, 12, 11 first
slice, 9; medium = 13, 5, 4; large = 7, 11 second slice; largest = 8, 10,
15. Size is a guess at the number of coherent green slices, not a promise.

When a boundary has many callers, first run the package 0 census. A successful
fallback attempt does not prove that a fixture needs it; rerun with only that
route denied before designing new evidence. Temporary probes and denial
switches must not land.

## Protocol for agents taking a package

- Work in a dedicated worktree and branch named for the package, for example
  `claude/simplify-kernel-pkg-03-quantities`. Follow `AGENTS.md`: the primary
  checkout is integration-only.
- Read this file, `docs/concepts/smart-and-simple-tactics.md`,
  `docs/internals/verification-efficiency.md`,
  `docs/internals/testing.md`, and `docs/concepts/proof-failure-triage.md`
  before editing.
- Do not reopen a boundary ruling. If one is unworkable for the package,
  stop, write up the evidence, and return the worktree to a green checkpoint.
- Do not edit C fixtures to expose a friendlier proof state. Adapt contracts,
  tactics, evidence, lowering, or kernel rules. Keep the original C and claim
  as the regression.
- Do not add rules to `decide` or the atomic checkers. Do not convert a
  `proves` site to `decide` unless the proposition is already a bare
  `ConditionIs`.
- Do not add a `ProofStep` variant that is smart or internal-only. Do not add
  a production `std::env` read under `src/kernel/`. Do not raise a time or
  work limit to make a fixture pass.
- Do not file issues. Report findings in the package report.
- Read the census section before designing evidence for a site. A site that
  never fires in the corpus needs a reaching fixture; a site whose successes
  are exact-covered needs a route restriction, not new vocabulary.
- Judge green only from an unpiped `scripts/check.sh` exit status. Both
  fixture harnesses must pass with the body-rerun census pinned at zero.
- The package report states: what landed, the census numbers before and after
  where relevant, the deterministic-work delta on profiled examples, any
  fixture whose proof text changed and why, and any dependency discovered on
  another package.
- Integrate only a green commit, by Git, onto a base that has not moved
  unexpectedly. If the base moved, rebase and rerun the affected gates.

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
- `PureFactContext::decide` and the atomic memory and resource checkers, under
  the freeze rule above, and their remaining whole-context scans, which are
  efficiency debts.
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
- Every remaining kernel rule above the atomic theory boundary has explicit
  named inputs and work bounded by those inputs, indexed evidence, and
  semantic output. `decide` and the atomic checkers are unchanged in rule set
  from `5c2ec4e8` except for deletions.
- Every smart success has complete provenance that expands to ordinary Surface
  Click containing only simple or structural operations, and the rewritten
  source verifies through the ordinary entry point. `ProofStep` has no smart
  or internal-only variant.
- Pure-theorem, call/refinement, resource, lowering/execution, and termination
  authority uses checked retained evidence or explicit obligations rather than
  rediscovering proofs. Retained evidence names premises, not contexts.
- Deadline or exact-cycle interruption cannot escape as an ordinary proof miss
  or poison a negative memo.
- No production `std::env` read or search-disabling switch exists under
  `src/kernel/`.
- `PureFactContext::proves` and `derive_proposition` no longer exist under
  `src/kernel/`.
- `scripts/check.sh` passes, both fixture harnesses pass with the contract
  fallback census at zero, and deterministic work over profiled examples does
  not regress.
