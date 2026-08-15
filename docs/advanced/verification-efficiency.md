# Verification Efficiency

Click is intended to verify existing programs at codebase scale. Fast examples
are not enough: deterministic verification of an explicitly certificated
project must remain approximately linear in the amount of C and Click that is
actually relevant to the selected proof units.

This is a correctness requirement for the proof-tool boundary. A simple proof
that becomes unusably slow as unrelated functions, facts, snapshots, or
resources are added is a verifier defect, even if it eventually succeeds.

## Complexity contract

Let `N` be the size of the selected C source, Click source, imported
definitions, and explicit certificate. Let `q` be the size of the input named
by one tactic, and let `d` be the amount of new proof state or certificate text
that the tactic must produce.

A simple tactic should take

```text
O((q + d) polylog N)
```

amortized work. In particular, it must not scan, compare, hash, or clone proof
state unrelated to the rule and evidence named by the tactic. A project made
entirely of simple tactics should verify in

```text
O((N + D) polylog N)
```

work, where `D` is unavoidable semantic output such as explicitly enumerated
execution paths or unfolded resource members. For ordinary straight-line,
modular code, `D` should itself be linear in the source and certificate.

`O(log N)` is shorthand for indexed access, not permission to ignore input or
output size. Reading ten explicit premises costs at least ten operations;
unfolding a resource with ten members costs at least ten operations. The
violation is touching the other thousand facts, functions, snapshots, or
resources that the tactic did not name.

## Simple means locally checkable

A simple tactic checks one named proof rule from explicit evidence. Expansion
removes smart search by producing such a certificate. It cannot repair a
simple checker that performs global search, rebuilds its whole context, or
copies the complete project state at every step.

Simple checking may perform bounded work over:

- the tactic and its explicit premises;
- the affected C expression or statement;
- the resource or predicate body explicitly being opened or closed;
- the proof-state delta produced by that operation; and
- indexed lookups into immutable ambient environments.

It may not, by default:

- clone a complete function environment, symbolic state, fact set, or history;
- linearly search all ambient facts for an exact named premise;
- enumerate all theorem facts for every function;
- materialize all pairwise separation facts in a resource context;
- rerun a theory prover once per unrelated premise merely to minimize a
  certificate; or
- use a bounded linear cache with deep structural comparison as the durable
  identity mechanism.

## Output-sensitive exceptions

Some verification work is inherently larger than one lookup. Its cost must be
charged to visible semantic output rather than hidden ambient state:

- A source branch can create two paths. Repeated branching may create many
  paths, but verification should share common prefixes and cost no more than
  the explicit path certificate it checks.
- A finite quantified proof may enumerate its declared finite range. The range
  and its bound must be explicit and enforced.
- Unfolding or folding may visit every member of the named definition, but not
  every definition in the project.
- A resource operation may inspect every resource explicitly consumed or
  produced. Separation and validity facts that follow from an indexed
  authority relation should remain implicit rather than be eagerly expanded
  into a quadratic set.
- Independent kernel certification may add a small constant multiple of the
  selected function's work. It must not multiply that work by the number of
  claims, unrelated functions, or globally declared theorems.

## Representation requirements

The complexity contract implies several design constraints:

- Large immutable environments and proof states need persistent structural
  sharing. A clone used to create one modified view should be constant or
  logarithmic in the shared structure.
- Propositions, terms, memories, functions, and environments used as cache
  keys need stable interned identities or cached content fingerprints. Cache
  lookup must not traverse the object whose computation it is intended to
  avoid.
- Fact stores need exact indexes plus theory-specific secondary indexes. For
  example, condition, quantified, memory/loadability, and resource facts must
  be discoverable without scanning all proposition kinds.
- Derived relations such as contradiction, order reachability, resource
  coverage, and separation should be maintained incrementally or queried from
  indexed base facts.
- Each function should receive the transitive dependencies it references, not
  a copied global environment or every theorem in the project.

These constraints are semantic-neutral. They must preserve independent kernel
checking and must never turn an unproved, failed, or deadline-limited result
into a cached success.

## Lazy separation and compact composition carriers

Resource contexts never materialize pairwise `CResourceSeparate`
propositions. A multi-owner context exposes one compact
`CResourceComposition` carrier, and separation queries — range and pointer
disjointness, subrange inheritance — are answered from the carrier's
projection with indexed per-query work
(`symbolic_same_block_ranges_emit_no_pairs_with_near_linear_work` pins the
projection curve). Consumers that need a separation *proposition* — a
certificate premise, a have-proof `assumption` goal — ask the prover, which
serves it from the carrier on demand; the proposition is materialized only
at that ask, never into ambient fact sets. Adding a valid carrier must be
monotone for already-provable snapshot premises
(`added_composition_carrier_keeps_snapshot_premise_work_bounded`).

The pairs' accidental effectiveness came from restating each fact in every
term vocabulary that ever existed, so lookup never proved cross-snapshot
equality. The replacement attacks term identity directly:

- **Stratified derivation edges.** A snapshot's derivation is described in
  its parent's vocabulary; call-havoc footprints are canonicalized at
  recording so later frame queries match entry-vocabulary facts
  syntactically.
- **Canonicalize at creation, bounded guards.** Terms adopt a ground-equality
  representative only when it strictly lowers the term (fewer memory loads,
  or a constant for a non-constant). Same-shape respellings are rejected —
  consumers that structurally re-derive recorded ranges must keep seeing the
  original vocabulary.
- **Bridge at the availability boundary.** A fact and a premise that spell
  one condition over different snapshots are decided by the snapshot bridge
  (candidates only from available facts, both normalized and original
  spellings tried), never by re-storing per-vocabulary copies.
- **Write-set fingerprints.** Call-havoc markers carry a spelling-invariant
  fingerprint of their write set in the marker block size, so
  alpha-colliding claims whose same-named havocs wrote different shapes stay
  content-distinct in the interning arena; the residual same-shape collision
  and the claim-scoped salt design are recorded in the issue tracker's
  history.
- **Explicit `rewrite` stays the completeness escape hatch**, and the
  long-run trajectory for recurring snapshot-equality gaps is a forkable,
  provenance-carrying e-graph fed by executor-discharged guard equalities —
  never by guard search.

## Indexed contradiction and premise search

Derived contradiction checking and condition premise search follow one
pattern: per-term facts fold into indexes once, and genuinely pairwise proof
work runs only where a theory rule's own first-line requirements say a pair
could relate.

Context inconsistency labels the equality graph's connected components once
per check and extends them with depth-bounded canonical endpoint forms:
resolved loads, folded constants, sorted addends, collapsed single-addend
sums, and canonical memories for unresolved loads. Each canonicalization step
is justified by a kernel equality, so a strict order edge inside one class, or
a reverse edge between two classes, is a contradiction found by map lookup.
The remaining deep comparisons are bucketed by rule requirements — loads with
loads, sums under equal folded constants and addend counts, conditionals with
conditionals, folds with fold splits — and every performed comparison uses the
unchanged proof-aware equality. Pin regressions fix each preserved reach:
additive commutativity, load resolution, cross-snapshot load bridging, and
graph-equal addends inside the add rule. Same-bucket contexts are still
compared pairwise; that width is bounded by rule-relevant facts, not by the
ambient context.

Condition premise search tries single candidates, then candidate pairs that
some derivation could connect: two facts sharing a bitvector variable
(collected through load pointers and memories, so snapshot spellings still
connect) or two facts each sharing one with the goal. A pair sharing neither
is jointly satisfiable whenever each fact is, and a fact unsatisfiable alone
is found by the single-candidate pass, so the skipped pairs hold no
derivation. Wider premise sets come from one derivation over the complete
candidate set minimized to its actual dependencies. Quantified matching
remains a per-query linear scan over quantified facts; its curve guards
against that scan acquiring a superlinear axis.

The deterministic gates for these paths hold one fixed decision or derivation
while growing unrelated context: exact contradiction, consistent order
contexts, theory-capable order endpoints, fixed overflow decisions, quantified
fact queries, long order paths, fixed loadability queries, and condition
derivations.

## Checked execution reuse

Proof replay and opaque-contract certification may share function-body work
only through `CCheckedFunctionExecution`, a kernel-created artifact. The
artifact seals the exact entry state, annotated function, arguments,
environment, execution semantics, loop judgment, assumptions, and complete
checked frontier. Its fields are private to the kernel; a proof planner can
retain and present the artifact but cannot manufacture its authority.

At the opaque-contract boundary, the kernel reconstructs contract assumptions
and resource-guard cases independently. It reuses an artifact only when all
sealed structural inputs and reasoning-policy flags match and every sealed
premise is proved by that reconstructed contract context. A limited or empty
frontier is never reusable. Any mismatch performs fresh symbolic execution.
Thus reuse removes duplicate C-body interpretation without trusting smart
search state or weakening independent contract checking.

Proof-directed folds, unfolds, and observations may give the checked artifact
a different ghost `ResourceContext` from the independently reconstructed
contract entry. For non-recursive resource definitions, the kernel may rebase
the artifact only after checking that locals, memory, and counted populations
are exact and that its bounded resource-equality relation proves the two ghost
contexts definitionally equal. Recursive resource representations do not enter
that relation as a cache probe: until they have stable shallow identities they
fall back immediately to fresh execution.

Likewise, two complete artifacts checked under exactly opposite polarities of
one entry condition may be composed into one exhaustive frontier. All other
premises must follow from the reconstructed contract context and every sealed
execution input must match. One side alone, two unrelated conditions, or any
additional unproved premise forces fresh execution.

Grouped claims retain the same artifact, so adding claims does not multiply
whole-function execution. Tests count checked body executions directly and
also require an artifact containing an unproved extra assumption or an
incomplete entry partition to be rejected.

## Regression policy

Wall-clock examples find user-visible pain, but they do not enforce a scaling
law. Performance-sensitive changes need deterministic scaling regressions that
generate at least four sizes, normally `N`, `2N`, `4N`, and `8N`, and measure
verifier work rather than host time.

Each sample also records deterministic work attributed to named verifier
operations and tactic kinds. A failed growth curve must report those named
curves so the aggregate regression points to the responsible checker or phase;
wall-clock profiler attribution is corroboration, not the scaling authority.

The scaling suite should cover independent axes:

- number of unrelated functions and verified rules;
- straight-line statements and program-point snapshots in one function;
- ambient pure and condition facts;
- surface-to-kernel proposition spellings;
- resource facts and resource-definition members;
- global and imported theorem declarations; and
- number of claims sharing one function execution.

For a linear or `N log N` path, doubling the input should remain close to a
factor of two after fixed startup work is excluded. A regression must fail on
the old representation and pass on the new one. Absolute corpus timings are
useful corroboration, not a substitute for the scaling assertion.

Any new hot-path collection, cache, or clone should answer these review
questions:

1. What is its size in terms of source or certificate input?
2. Is lookup indexed by the exact semantic key?
3. Does mutation share unchanged structure?
4. Can one operation enumerate unrelated entries?
5. What scaling regression protects the claimed bound?

See [Testing Click](testing-click.md) for commands, budgets, and profiling.
The open implementation work is ordered in [`issues/README.md`](../../issues/README.md).
