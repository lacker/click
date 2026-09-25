# Verification efficiency

Click is intended to verify existing programs at codebase scale. Fast examples
are not enough: deterministic verification of a project written with explicit
proofs must remain approximately linear in the amount of C and Click actually
relevant to the selected proof units.

This is a correctness requirement for the proof-tool boundary. A simple proof
that becomes unusably slow as unrelated functions, facts, snapshots, or
resources are added is a verifier defect, even if it eventually succeeds.

## Complexity contract

Let `N` be the size of the selected C source, Click source, imported
definitions, and explicit proof text. Let `q` be the relevant input inspected
by one tactic: its explicit operands and premises, the affected program
operation or definition body, and indexed context entries needed by that
operation. Let `d` be the amount of new proof state or expanded proof text that
the tactic must produce.

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
modular code, `D` should itself be linear in the source and explicit proof.

`O(log N)` is shorthand for indexed access, not permission to ignore input or
output size. Reading ten explicit premises costs at least ten operations;
unfolding a resource with ten members costs at least ten operations. The
violation is touching the other thousand facts, functions, snapshots, or
resources that the tactic did not name.

## Simple means locally checkable

A simple tactic checks one selected proof operation deterministically, without
planning or search. Expansion removes smart search by producing such an
explicit proof. It cannot repair a simple checker that performs global search,
rebuilds its whole context, or copies the complete project state at every step.

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
- rerun a theory prover once per unrelated premise merely to minimize an
  expanded proof; or
- use a bounded linear cache with deep structural comparison as the durable
  identity mechanism.

A statement step is the canonical instance. It carries no fact by list: the
kernel executes the statement with the whole proof context visible, reading
it through the proof object's persistent indexed `PureFactContext` (no
materialized fact list), and a cell the context proves outside the effect
keeps its name, with ownership consulted by direct lookup only. A fact about
a cell it cannot prove untouched stays at its pre-step snapshot; an explicit
`transport` pays for anything more. Term comparison performs no
frame reasoning. The user-facing statement of this rule is
[What a step carries](../concepts/proof-state.md#what-a-step-carries).

## Output-sensitive exceptions

Some verification work is inherently larger than one lookup. Its cost must be
charged to visible semantic output rather than hidden ambient state:

- A source branch can create two paths. Repeated branching may create many
  paths, but verification should share common prefixes and cost no more than
  the explicit path structure it checks.
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
- Termination height inference reads the forward call closure of the run: the
  bodies of the functions this run verifies, plus the contract-less
  `static inline` helpers those bodies reach, each read once. This is the one
  termination cost that is not per-function local, and it is charged to
  visible input and output — that closure is the selected syntax, and a
  height for each of its nodes is the planner's whole result. Every other
  part of the check reads one function's own call sites and loops. See
  [Termination heights and local descent](#termination-heights-and-local-descent).
- A loan-preserving havoc (loop head, interface join) decides, per surviving
  cell, whether an active loan protects it. Concrete protected ranges answer
  from the dyadic index; a range with a symbolic base or bounds cannot be
  indexed, so the query walks its block's symbolic bucket, and the havoc
  costs cells times symbolic loans in that block. Neither count is output the
  havoc must produce, so this is a known violation of the contract rather
  than an exception, pinned as a measurement
  (`loop_head_havoc_work_over_cells_and_symbolic_loans` in
  `src/kernel/proof/execution.rs`: 65, 257, 1025, and 4097 units for 8, 16,
  32, and 64 of each). Removing it needs a secondary index over symbolic base
  terms, or a havoc narrowed to a checked write set so most cells are never
  queried. The fixed dyadic walk the query used to pay per cell is gone: with
  no concrete range registered the walk can only return the empty set and is
  skipped. Interface-join binding inheritance, by contrast, compares the
  successor's bindings against the arms' through one membership index over
  binding values and is linear in the binding count, which grows with proof
  length (`interface_binding_inheritance_is_near_linear_in_the_binding_count`).
- An explicit fold read frame — a `transport` of a fact about an application
  of a checked range-fold function (`src/kernel/fold_read_summary.rs`) —
  walks the recorded memory history back from both array snapshots to a
  common one and decides each step it crosses once, from that step's own
  write set and exact order or separation lookups. The steps are the frame's
  semantic output; nothing is recorded or memoized, so the next transport
  pays only for its own steps. Summary checking is one unit per node of the
  declared body, once per verification. The kernel tests pin 74, 138, 266,
  and 522 units for 8 to 64 counted reads in the body; 175 to 1,407 units
  for 8 to 64 framed applications; 17 units whether 64 or 512 unrelated order
  facts sit beside one framed store, and whether the interval holds ten or a
  billion cells; and 272 to 2,176 units for 16 to 128 stores each crossed by
  its own transport. The surface regression
  `explicit_fold_read_transport_along_a_store_sequence_is_near_linear` pins
  the whole verification at 4 to 32 stores.

## Execution capacity follows selected syntax

The ordinary kernel execution APIs seed expression and statement capacity with
the evaluator-visible structural cost of the selected C expression, statement,
or function body. A whole-function seed also includes its caller-side argument
expressions. This source allowance covers one non-amplified traversal of that
syntax, including each evaluator layer structurally required by the selected
judgment; it is not a fixed project-wide source-length cap.

The existing fixed reserve remains separate and pays for repeated dynamic work:
loop iterations, executed callee bodies, short-circuit or branch amplification,
and any other evaluator visit beyond the selected syntax baseline. Function-call,
loop-unroll, and maximum-path-width limits remain independently enforced.
Consequently, adding explicit straight-line source increases capacity only in
proportion to that source, while repeatedly executing a small source fragment
still reaches a bound.

APIs whose names end in `with_budget` preserve the caller's exact budget and do
not add source capacity. These are the kernel escape hatch for adversarial and
resource-constrained checks; changing the ordinary source-sized default does not
weaken their limits.

## Representation requirements

The complexity contract implies several design constraints:

- Large immutable environments and proof states need persistent structural
  sharing. A clone used to create one modified view should be constant or
  logarithmic in the shared structure.
  Kernel memory snapshots follow this: their maps are persistent B-trees
  with cached content hashes, so a store and the interning of its result are
  logarithmic in unrelated memory (see [Memory derivation DAG](memory-dag.md)).
  A fact context's stated propositions are a persistent ordered set too:
  lowering and planning clone a context and extend it by a fact at every
  path, and a shared copy-on-write set made each extension copy every stated
  proposition.
- Propositions, terms, memories, functions, and environments used as cache
  keys need stable interned identities or cached content fingerprints. Cache
  lookup must not traverse the object whose computation it is intended to
  avoid.
- Fact stores need exact indexes plus theory-specific secondary indexes. For
  example, condition, quantified, memory/viewability, and resource facts must
  be discoverable without scanning all proposition kinds. An index whose key
  is expensive may be deferred to its first query when each fact change is
  still keyed at most once: a fact context's stated-proposition index records
  its changes on a persistent chain, and a query keys only the suffix no
  earlier query on a shared ancestor built, so contexts a planner rebuilds
  from fact lists and never asks cost no keys at all.
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
propositions, and neither do the fact contexts that hold them. A multi-owner
context exposes one compact `CResourceComposition` carrier. Holding it states
nothing further: a separation query — range and pointer disjointness,
subrange inheritance, a store crossing a cached cell, two distinct range
anchors — asks each held composition for two distinct owned members of the
query's block, one holding each side
(`ResourceContext::separated_owned_members_in_block`, and
`separates_owned_anchors` for anchors). Each owned member of that block is
asked once whether it holds the first side and, only when one does, once
whether it holds the second, so a query costs the block's members and never
their pairs. The anchor question is two keyed lookups in the composition's
anchor index. The candidates are exactly the pairs the carrier used to
project into every fact context at insertion (two owned ranges of a block
holding two or more, not already structurally separate, in a block whose
ranges do not all share one concrete base), so the answers are unchanged;
only the pairwise projection, `N(N-1)/2` entries for `N` owned ranges of one
block, is gone. The `ExternalArgument` block makes that cost real: every
object a pointer parameter reaches shares it
(`holding_a_parameter_composition_states_no_pairs` and
`one_parameter_separation_query_is_linear_in_the_owned_objects` in
`src/kernel/tests/resource_scaling_tests.rs`: 37, 137, 529, and 2,081 units
to hold 8, 16, 32, and 64 owned parameter objects, now 0; a refused
separation query 985 to 68,801 units, now 321 to 2,617). Consumers that need
a separation *proposition* — an explicit premise, a have-proof `assumption`
goal — ask the prover, which serves it from the carrier on demand; the
proposition is materialized only at that ask, never into ambient fact sets.
Adding a valid carrier must be monotone for already-provable snapshot
premises (`added_composition_carrier_keeps_snapshot_premise_work_bounded`).

Deciding that a context is a valid partition reads the same indexes. Only an
identity held twice or with invalid access, a block owning two or more
ranges, or a base that an exact pointer equality joins to another block can
hold a violation, so a call composing its ensured resources into a caller
frame never visits the caller's unrelated allocations
(`src/kernel/tests/resource_scaling_tests.rs`).

Within one block, an owned range is compared only with the owned ranges a
fact could relate it to (`ResourceContext::owned_validity_candidates`). A
base's *root* is its block and the first symbolic atom of its offset in
canonical form (`p` for `p`, `p + 8`, and `p + 4*i`; nothing for a constant
offset), and the ranges are indexed by root. A range is compared with the
ranges at its own root, at the roots its base's same-block exact aliases
have, at the roots that scale a member of its root index term's
recorded-equality class (a member pinned to a constant reaches the block's
constant-offset bases), at a base with a same-block exact alias at one of
those roots, and at the exact bases of its cross-block aliases. Two ranges
at unrelated roots — two pointer parameters `4*a` and `4*b` with no fact
relating `a` and `b` — are not compared. The overlap decision
(`memory_ranges_proven_overlapping`) rebases through exact aliases and then
proves the endpoints under the structural base delta, here `b - a`, which is
bounded only by a fact relating the two index terms. They may alias, but
validity is a refusal of a *proven* overlap, not a proof of disjointness, so
an overlap no fact states needs no work: skipping it can only admit a
composition whose overlap nothing proves, and every resource in a
composition comes from a transfer rule that never duplicates ownership, so
no authority is created. The explicit-separation veto inside the decision
runs only after the endpoints prove an overlap, which a valid composition
never does. Composing one more parameter object costs 2 units at 8 to 64
owned parameter objects (959 to 61,439 before, each pair searching the
projected pairs), and a whole-frame check is linear
(`composing_a_parameter_object_ignores_unrelated_parameters`,
`validity_of_parameter_objects_is_linear`); the relating facts are pinned
by `parameter_validity_still_refuses_related_overlaps`.

The pairs' accidental effectiveness came from restating each fact in every
term form that ever existed, so lookup never proved cross-snapshot equality.
The replacement gives terms one canonical identity and makes state changes
explicit:

- **Stratified derivation edges.** A snapshot's derivation is described in
  its parent's vocabulary; call-havoc footprints are recorded in
  assumption-free canonical form. A later frame proof that needs another
  vocabulary supplies an explicit `frame using` restatement rather than
  changing the stored footprint.
- **Canonicalize at creation.** A memory load becomes the load variable for
  its cell epoch where lowering or symbolic execution creates it. Condition-fact
  availability is therefore exact canonical-form lookup; it never searches
  ambient facts for a cross-snapshot match. Separation facts use a
  snapshot-independent shape index only to select candidates, after which the
  kernel must prove the range relationship from frame evidence. The full term
  invariant is in [Canonicalization](canonicalization.md).
- **Transport facts at statement boundaries.** A statement step carries only
  the selected or automatically considered facts whose direct frame check
  succeeds. More general cross-snapshot reasoning is an explicit `transport`
  proof step, not a comparator side effect.
- **Rewrite snapshots by identity.** Load terms carry snapshots and snapshots
  hold load terms, so terms reach a snapshot *DAG*. Substituting a variable
  visits each interned snapshot once for that substitution, and the fact set a
  memory load reasons under stays the caller's object so the load's alias
  queries keep an ambient memo identity. Both are pure-function memoizations
  over stable interned ids, not new proof authority.
- **A smart closure asks each failed question once.** A `simp` attempt
  can reach one goal through several strategies and candidates; the snapshot
  transport closure lowers the goal at every recorded snapshot, and every
  snapshot holding the goal's cells unchanged lowers it to the same source.
  Inside one attempt (`with_closure_failure_memo`) a fact-transport
  reachability check, a load-variable bridge check, and a pointer-distinctness
  query that failed are remembered by their exact inputs, the content id of
  their fact set, the memory-DAG generation, the DAG scope modes, and the cell
  lookups in progress, and a repeat fails without being recomputed. Failures
  that met a cycle cut or a limit are not remembered and nothing outlives the
  attempt, so the memo changes a failing search's cost, never its outcome
  (`mdtests/simp_frame_failure_through_region_arena_is_prompt.md`, pinned
  below the default budget by the mdtest harness).
- **Decide an overlap before searching for a separation.** A walk across a
  call asks whether each cell it names is separate from the callee's write
  set. A cell the write set contains, such as a field of an object that a
  range spells through an alias (`arena + 16` against `x[4..5)` under
  `arena == x`), is decided inside it by that one alias and the constant
  displacement, before any range's separation search runs, and a call's
  kept ranges are placed by the ranges spelled through the access's own
  bases first, with each proved base equality to another kept range asked
  once per fact set.
- **Write-set fingerprints.** Call-havoc markers carry a representation-invariant
  fingerprint of their write set in the marker block size, so
  alpha-colliding claims whose same-named havocs wrote different shapes stay
  content-distinct in the interning arena.
- **Explicit proof steps remain the completeness escape hatch.** `rewrite`
  uses a proved equality, while `transport` uses checked frame evidence. The
  canonical comparator itself uses neither.

## Indexed contradiction and premise search

Derived contradiction checking and condition premise search follow one
pattern: per-term facts fold into indexes once, and genuinely pairwise proof
work runs only where a theory rule's own first-line requirements say a pair
could relate.

Context inconsistency labels the equality graph's connected components once
per check and extends them with a complete, context-local order-endpoint index
key: it follows every finite resolved-load hop, folds constants, sorts
addends, collapses single-addend sums, and uses the assumption-free form for
unresolved loads. This is purpose-specific indexing, not canonical identity.
Each key transformation is justified by a kernel equality, so a strict order
edge inside one class, or a reverse edge between two classes, is a
contradiction found by map lookup.

The remaining deep comparisons are selected by complete necessary-condition
residues — loads with loads, sums under equal folded constants and addend
counts, conditionals with conditionals, folds with fold splits — and every
performed comparison uses the unchanged proof-aware equality. Residues may
admit extra candidates but cannot omit a pair accepted by a theory rule. Pin
regressions fix each preserved reach: additive commutativity, finite load
resolution chains beyond the former depth-six cutoff, cross-snapshot
canonical forms, and graph-equal addends inside the add rule. Same-residue
contexts are still compared pairwise; that width is bounded by rule-relevant
facts, not by the ambient context.

A condition-fact query reads the facts filed under the keys it spells
(`PureFactContext::has_condition_fact`). The fact itself is an exact lookup.
A differently spelled fact that `condition_matches` accepts is filed under
its kind and the canonical forms of its two sides (an equality under its
unordered sides, a signed order under its strictness and its lower and upper
side whichever way it was written), and the query reads the keys its own
sides and their recorded-equality classes spell. A fact with a side that is
not an atom (a load, a sum, a conditional) can match through reasoning its
key does not spell, such as a load's stored value, so those facts of the
query's kind stay a scanned fallback, charged one unit each; a fact of two
atoms is never visited by a query that does not spell its key. The ordering
that matches modulo canonical load atoms is the query's own canonical key,
and the symbolic-block hop of range membership reads the exact pointer
equalities filed under its pointer. With 64 to 512 unrelated atomic facts,
the five queries of `condition_fact_queries_ignore_unrelated_facts`
(`src/kernel/tests/memory_scaling_tests.rs`) examine 3 facts in all; they
examined 265 to 2,057 before.

A term's constant after equality normalization is a lookup in
`ConstantClasses` (`src/kernel/assumptions/constant_classes.rs`), which the
fact context maintains on every true 32-bit equality it files. Each class
carries the merge of its members' folded constants as `Known(c)`,
`Ambiguous`, or `Unknown`; a union merges two classes' constants, so two
different constants in one class are still ambiguous, and a class whose
constant rises re-folds only the compound terms that use one of its members.
A constant only rises, so each registered term is re-folded a bounded number
of times along one path. A query no longer walks the facts connected to the
term: before, a counter advanced by `N` calls re-walked its whole chain at
every call, deep-comparing every same-address load at another snapshot, so
the `N`th call cost `O(N^2)`. Only an `Unknown` class does query-time work:
its conditional members are decided, and its loads are compared with the
loads of settled classes at the same memory-blind address. The regression
is `counter_call_chain_ensure_lowering_stays_flat_per_call`
(`src/surface/tests/scaling_tests.rs`).

Condition premise search tries single candidates, then candidate pairs that
some derivation could connect: two facts sharing a bitvector variable
(collected through load pointers and memories, so snapshot forms still
connect) or two facts each sharing one with the goal. A pair sharing neither is
jointly satisfiable whenever each fact is, and a fact unsatisfiable alone is
found by the single-candidate pass, so the skipped pairs hold no derivation.
Wider premise sets come from one derivation over the complete candidate set
minimized to its actual dependencies. Quantified matching remains a per-query
linear scan over quantified facts; its curve guards against that scan acquiring
a superlinear axis.

The deterministic gates for these paths hold one fixed decision or derivation
while growing unrelated context: exact contradiction, consistent order
contexts, theory-capable order endpoints, fixed overflow decisions, quantified
fact queries, long order paths, fixed viewability queries, and condition
derivations.

## Termination heights and local descent

Whole-project termination is decided in two passes over one call graph, built
once from the run's verified functions and the inline helpers they reach.
`c_termination_height_plan` proposes a height per node — iterative Tarjan with
an explicit stack, longest path over the condensation, cycle members sharing a
height. `c_verified_function_termination_rules` then checks that proposal:
functions are grouped by planned height and levels are settled in ascending
order, so at each call site the check reads only whether the callee is above
its caller, whether a strictly lower callee already has evidence, and whether
an equal-height callee is a recursive edge that a declared measure ranks. A
refused member of a level withdraws its same-level callers through a worklist
that pops each refusal once and reads each intra-level edge once.

Calls through function pointers add one body walk and at most one more
settling pass, not a search. Each function's body and linked static
initializers are walked once for the addresses they take. The first settling
pass refuses every pointer call, so what it certifies returns without going
through a function pointer; when every address taken names such a function,
a second pass over the same levels lets pointer calls return. A run with no
pointer call never takes the second pass.

The contract is therefore work linear in the call graph's nodes and edges,
up to the indexing factor of the name-keyed BTree containers. Neither pass
performs a reachability search, and no function's check scans another
function's state; the plan is untrusted, so a wrong height can only refuse a
function or fail the check, never certify one. The predecessor of this design
found recursive components by pairwise reachability and was roughly cubic.

`termination_scaling_tests` in `src/kernel/termination.rs` pins the curve over
five graph shapes at 500, 1,000, 2,000, and 4,000 functions, asserting the
verdicts at each size so the curve cannot be flattened by a run that decides
nothing. It counts cooperative checkpoints — body statements walked, call
edges read, level members settled, planner visits, worklist steps — not host
time. Measured units, planner then check: a single call chain, the deepest
graph, costs 5,996/6,498, 11,996/12,998, 23,996/25,998, and 47,996/51,998; a
layered DAG with four callees per function, where edges outnumber nodes,
costs 20,896/24,392, 41,728/48,696, 83,728/97,696, and 167,728/195,696. Wide
fan-out, many small unmeasured cycles with their callers, and one large cycle
of the whole run measure the same exact doubling. The assertion allows a
threefold rise per doubling, which leaves room for the indexing factor while
rejecting the fourfold rise of a quadratic checker.

## Checked execution reuse

Ordered finalization and opaque-contract certification may share
function-body work only through `CCheckedFunctionExecution`, a
kernel-created artifact. The
artifact retains the exact entry state, annotated function, arguments,
environment, execution semantics, loop judgment, assumptions, and complete
checked frontier. Its fields are private to the kernel; a proof planner can
retain and present the artifact but cannot manufacture its authority.

At the opaque-contract boundary, the kernel reconstructs contract assumptions
and resource-guard cases independently. It reuses an artifact only when all
retained structural inputs and reasoning-policy flags match and every
retained premise is proved by that reconstructed contract context. A limited or empty
frontier is never reusable. Every reusable artifact becomes one path set of
the case, and a claim is certified when one path set certifies it on every
path; a set is prepared for claim checking only when a claim is judged over
it, so a claim the first set certifies never prepares the second.
Certification never executes the body: when no artifact can be reused it
produces no paths and the reason. Thus reuse removes duplicate C-body
interpretation without trusting smart search state or weakening independent
contract checking.

Proof-directed folds, unfolds, and observations are retained as checked
zero-source execution events. Each event names its exact input state,
registered composite definition, and output resource/fact delta, so final
completion follows the event without interpreting the C body again. At contract
entry, a non-recursive representation may still be rebased only after checking
that locals, memory, and counted populations are exact and that the bounded
resource-equality relation proves the two ghost contexts definitionally equal.
Recursive resource representations do not enter that relation as a cache
probe: until they have stable shallow identities they fall back immediately to
fresh execution.

Likewise, two complete artifacts checked under exactly opposite polarities of
one entry condition may be composed into one exhaustive frontier. All other
premises must follow from the reconstructed contract context and every
retained execution input must match. One side alone, two unrelated conditions, or any
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
- global and imported theorem declarations;
- number of claims sharing one function execution; and
- call-graph nodes and edges in whole-project termination checking.

For a linear or `N log N` path, doubling the input should remain close to a
factor of two after fixed startup work is excluded. A regression must fail on
the old representation and pass on the new one. Absolute corpus timings are
useful corroboration, not a substitute for the scaling assertion.

Any new hot-path collection, cache, or clone should answer these review
questions:

1. What is its size in terms of source or explicit-proof input?
2. Is lookup indexed by the exact semantic key?
3. Does mutation share unchanged structure?
4. Can one operation enumerate unrelated entries?
5. What scaling regression protects the claimed bound?

See [Testing Click](testing.md) for commands, budgets, and profiling.
The open implementation work is ordered in
[`issues/README.md`](https://github.com/lacker/click/blob/master/issues/README.md).
