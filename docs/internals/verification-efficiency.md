# Verification efficiency

Click is intended to verify existing programs at codebase scale. Fast examples
are not enough: deterministic verification of a project written with explicit
proofs must remain approximately linear in the amount of C and Click actually
relevant to the selected proof units.

This is a correctness requirement for the proof-tool boundary. A simple proof
that becomes unusably slow as unrelated functions, facts, states, or
resources are added is a verifier defect, even if it eventually succeeds.

[Verifier design](verifier-design.md) defines the split between the fast part
(checking: symbolic execution, the fact store, condition decisions, memory,
resources, simple tactics, certificates) and the slow part (smart tactics and
search helpers, bounded and expandable), and the rule that a fast-part
operation does indexed lookups and never scans a growing collection. This
page gives the formal contract and describes how the main operations meet it.
The operation inventory in [the smart-tactics roadmap item](https://github.com/clicklang/click/blob/master/roadmap/smart-tactics.md)
distinguishes tested routes, source candidates, deferred evidence and coverage
gaps. The guarantees below apply to their named routes; they do not establish
that every checking operation already satisfies the contract.

## Complexity contract

Let `N` be the size of the selected C source, Click source, imported
definitions, and explicit proof text. Let `q` be the relevant input inspected
by one operation: a tactic's explicit operands and premises and the affected
program operation or definition body. Index entries count toward this input
only when their traversal is justified by those operands or necessary changes;
a key selecting a large ambient bucket does not make that bucket explicit
input. Let `d` be the amount of new proof state or expanded proof text that
the operation must produce. Eager derived facts or internal cache rebuilding
do not become necessary output merely because the implementation emits them.

A fast-part operation, including every simple tactic, takes

```text
O((q + d) polylog N)
```

amortized work. It must not scan, compare, hash, or clone proof state
unrelated to the rule and evidence the operation names. A project made
entirely of simple tactics verifies in

```text
O((N + D) polylog N)
```

work, where `D` is unavoidable semantic output such as explicitly enumerated
execution paths or unfolded resource members. For ordinary straight-line,
modular code, `D` is itself linear in the source and explicit proof.

`O(log N)` is shorthand for indexed access, not permission to ignore input or
output size. Reading ten explicit premises costs at least ten operations;
unfolding a resource with ten members costs at least ten operations. The
violation is touching the other thousand facts, functions, states, or
resources that the operation did not name.

Work must also be deterministic. Candidate buckets and index reconstruction
iterate in admission order (pointer-class fact sources, pointer designations,
and opaque-extent aliases each retain an admission ordinal); allocation
addresses and state hash order never decide which candidate a
short-circuit search tries first, because that changes charged work between
identical runs. Trace source locations are resolved together in one source
walk per claim and shared by every step.

## Construction, not re-validation

Efficiency outranks the size of the trusted base. A proof-object operation
builds its successor from the branch's own state and is valid by
construction; nothing afterwards re-validates what the same session produced.
Producing evidence in one place and admitting it through a checker that
re-derives it (walking a theorem's premises against the context it was proved
under, re-comparing states the producer started from, recomputing an identity
the producer recorded) costs the work twice, and the second pass is usually
the one that grows with the path. Trusted-base size, untrusted callers, and
defense in depth do not justify it: if a caller could supply bad input, the
computation belongs inside the operation. Independent checking belongs only
where the input genuinely comes from outside the session, such as expansion
checks, audits, and certificates read back from disk, which run off the
simple-checking path.

The review question for any change is: does this re-validate something the
same session produced? If so, restructure it so the producing operation is the
only one. Existing produce-then-check code is a defect, tracked in
[`roadmap/scaling.md`](https://github.com/clicklang/click/blob/master/roadmap/scaling.md)
cause 4.

Current instances of the rule:

- A named-instance fold constructs its successor, checked facts, and
  execution event together
  (`ExecutionProofCore::fold_resource_instance_with_children`); recording
  never lowers the body again
  (`constructing_an_instance_fold_pays_for_its_body_once`).
- A logical case partition retains each arm's indexed context with its exact
  premise delta, and entering an arm shares it.
- Branch-interface publication extends one `ProofFacts` context as it
  exports facts; each assertion lowers against the accumulated context.
- An interface join combines the effects each arm's checked walk retained and
  does not reconstruct store or call-havoc results
  (`a_checked_interface_join_does_not_reconstruct_a_calls_havoc`).
- Loop-frame reconstruction checks each retained fact as it is composed and
  normalizes the completed resource context once.
- A narrow integer read constructs its certified type-range facts directly
  rather than re-proving them by order reasoning.
- An explicit outcome closer searches once; its failure explanation does not
  rerun `solve` or the implicit closer. Failed condition-target questions use the
  closure-scoped failure memo.
- Explicit return closers lower the folded claim goal once, and the unfolded
  form only when the proof unfolded a predicate. Consecutive exact return
  closers share one lazy `FunctionEnsureGoalContext`; any other tactic
  discards it. There is no global cache or structural state comparison.
- A whole-cell memory query first uses its address-class index; an exact
  supplier needs no resolution of the queried pointer's defining read.
- A refused separation of fixed fields on independent pointer parameters
  selects candidates through `ResourceContext::owned_memory_candidates_at`,
  which files fixed footprints by their scalar base variable. A query whose
  base is open (loaded, compound, constant-base, symbolically bounded) or
  named in a relating fact still retains its whole block; that conservative
  fallback is a known violation of the fast-part rule (see "Fast-part scans"
  in [the smart-tactics roadmap item](https://github.com/clicklang/click/blob/master/roadmap/smart-tactics.md)).

## Proof size and speed targets

The complexity contract says how verification must scale. These working
targets say what a finished example should look like. They are for judging a
proof and deciding where to look when one is slow, not gates.

- **Proof size:** at most about 20 lines of Click proof for each line of C it
  proves. This will not always be reachable, and expanding smart tactics
  moves a proof away from it, so treat it as tight.
- **Verification speed:** 700 or more proof lines per second is good, and
  about 300 is acceptable.

Measure the size first. A proof far over the size target is slow because it
is large, and the repair is in the proof or in a missing language feature,
not in the checker: the first complete `__rb_insert` proof was about 100
times its C and took 30 seconds at an acceptable rate per line. A proof near
the size target that verifies well under 300 lines per second points at the
verifier, and the complexity contract above applies. Report both numbers when
delivering an example.

`scripts/proof-ratio.py` measures the size of every example, and
`scripts/check.sh` prints the examples over the size target at the end of
each run, without failing. Lines and tokens both leave out comments and blank
lines, and code is the sources an example names in `verifying "...";`. The
report shows the token ratio beside the line ratio: a proof line is often
several times as long as a line of C, so a proof that puts many steps on one
line can meet the line target while its token ratio stays far over it.

Three examples stay over the target by maintainer decision (2026-10-17):
`rbtree-augmented`, `rbtree-erase`, and `rbtree-insert`, each between 35 and
40 times its C by lines when the decision was made. Each proves a Linux
red-black tree operation against a full model of the tree: parent pointers
packed with the color bit, the red-black and black-height invariants, the
in-order contents and, for `rbtree-augmented`, a subtree size kept by
callbacks. The rotations and recolorings come in mirrored left and right arms
that the C writes out separately, and the proofs follow the C rather than
refactoring it. The report keeps listing them, and an example that newly
crosses the target still needs its own reason.

## Simple means locally checkable

[Smart and simple tactics](../concepts/smart-and-simple-tactics.md) defines
the tactic classes. Expansion removes smart search by producing a simple
proof; it cannot repair a simple checker that performs global search,
rebuilds its whole context, or copies the complete project state at every
step.

Simple checking may perform bounded work over:

- the tactic and its explicit premises;
- the affected C expression or statement;
- the resource or predicate body explicitly being opened or closed;
- the proof-state delta produced by that operation; and
- indexed lookups into immutable ambient environments.

It may not:

- clone a complete function environment, symbolic state, fact set, or history;
- linearly search ambient facts for an exact named premise;
- enumerate all theorem facts for every function;
- materialize all pairwise separation facts in a resource context;
- rerun a theory prover once per unrelated premise merely to minimize an
  expanded proof; or
- use a bounded linear cache with deep structural comparison as the durable
  identity mechanism.

A statement step is the canonical instance. It carries no fact by list: the
kernel executes the statement with the whole proof context visible, reading
it through the proof object's persistent indexed `PureFactContext`, and a
cell the context proves outside the effect keeps its name, with ownership
consulted by direct lookup only. A fact about a cell it cannot prove
untouched stays at its pre-step state; an explicit `transport` pays for
anything more. Term comparison performs no frame reasoning. The user-facing
statement of this rule is
[What a step carries](../concepts/proof-state.md#what-a-step-carries).

Other operations follow the same shape:

- Observable resource compositions keep a persistent filtered storage root;
  producers advance only inserted or removed entries, and queries use
  maintained ownership counts rather than enumerating owners.
- Fixed-state propositions look up only the local bindings they reference in
  a recorded state.
- Logical reads through opaque pointers select an admitted footprint through
  the composition's class and interval indexes, without enumerating pointer
  spellings or scanning composition frames.

## Output-sensitive exceptions

Some verification work is inherently larger than one lookup. Its cost must be
charged to visible semantic output rather than hidden ambient state:

- A source branch can create two paths. Repeated branching may create many
  paths, but verification shares common prefixes and costs no more than the
  explicit path structure it checks. Path certificate merging advances
  borrowed cursors through checked steps and charges prefix comparisons,
  copied steps, and case traversal
  (`path_certificate_merge_work_is_bounded_by_its_input_steps`). Checked loop
  exits share immutable fact lists and their indexed context.
- A finite quantified proof may enumerate its declared finite range. The range
  and its bound must be explicit and enforced.
- Unfolding or folding may visit every member of the named definition, but not
  every definition in the project.
- A resource operation may inspect every resource explicitly consumed or
  produced. Separation and validity facts that follow from an indexed
  authority relation stay implicit rather than being eagerly expanded into a
  quadratic set.
- Independent kernel certification may add a small constant multiple of the
  selected function's work. It must not multiply that work by the number of
  claims, unrelated functions, or globally declared theorems.
- Termination height inference reads the forward call closure of the run once
  (see [Termination heights and local descent](#termination-heights-and-local-descent)).
- An explicit fold read frame (`src/kernel/fold_read_summary.rs`) walks the
  recorded memory history between the two array states and decides each
  crossed step once from its own write set; the crossed steps are its output
  (`explicit_fold_read_transport_along_a_store_sequence_is_near_linear`).
- An explicit quantified frame (`src/kernel/quantified_frame.rs`) walks source
  and target once in parallel, renames each binder once, and asks one checked
  load-history question per differing read; it never instantiates a
  quantifier (`quantified_frame_is_near_linear_in_unrelated_facts`).
- Typed range membership of an unsigned 64-bit index in a range with
  constant bounds (`PointerInRangeEvidence::UnsignedIndexed`) builds at most
  four spellings of the bound and looks each up exactly.
- A premise that is one conjunct of a recorded source fact's lowering is
  spelled through the surface proposition map's conjunct index.
- A store keeps every earlier cell of its block that it proves it misses.
  Constant byte gaps are decided by offset arithmetic over an anchor-ordered
  key range (`src/kernel/reasoning/store_gap.rs`), recorded strict signed
  orders form rank-indexed paths so a symbolic-index store visits only nearby
  ranks, and field stores beside separately owned parameter objects use a
  derived partition (`CellStore::parameter_partition_index`). Regressions:
  `stores_to_constant_indices_are_near_linear`,
  `symbolic_index_store_work_is_flat_across_recorded_order_chains`,
  `owned_parameter_field_store_work_is_flat`. General symbolic shapes still
  decide each unindexed cell individually, and union views are visited per
  candidate on every store; both are known violations of the fast-part rule.
- The initialization record (`InitializedBytes`) is never visited by a
  store: a store only adds to it, one run per block, and dropped runs are
  recorded per interval. A symbolic store invalidates a compact constant-value
  run by its possible index window.
- Every fact a context is built from is charged one unit
  (`PureFactContext::assume_proposition` and `assume_condition`), so a
  context rebuilt from a growing list shows as quadratic work. Path facts
  carry the contexts they build (`PureFactList`), extended by each step's
  additions; loop-invariant checking carries a prepared context between
  declarations and receives only the delta.
- Completed early-return paths retain shared fact prefixes and persistent
  candidate, evidence, and provenance vectors; terminal joins concatenate
  them instead of copying returned paths, finishing reads each retained trace
  by reference, and whole-claim expansion writes sequential returns one after
  another rather than nesting them
  (`completed_early_return_contexts_are_reused_for_certification`,
  `early_return_expansions_stay_flat_and_join_without_copying_paths`).
- Completion, contract path preparation, and outcome goals read each
  early-return path's context instead of rebuilding it from its prefix. The
  kernel extends a `CheckedPathContext` at each recorded transition by its
  context's projection diff, admitted case facts, and retained effects, and
  records it when a statement completes; kernel facts name their states,
  so earlier facts hold at the path's end. A dropped or changed fact, a
  changed reasoning policy or resource composition (a join, `branch
  ensuring`, a heap operation, a call), or a diff larger than the case facts
  and effects a restart would fold restarts it, and the restart defers that
  fold until as many transitions have recorded since or the path completes.
  The surface `EffectLeaf` holds each statement's facts with the path's
  effects, extended through `ProofFacts::introduced_since_within` up to the
  effects a rebuild refolds. Retained-trace walks visit each shared node once;
  surface path synthesis advances cursors instead of renumbering choices.
  Each path theorem still lists its own `k` premises, which is its output,
  charged to `path theorem premises` (62 to 8,642 units at 8 to 128 returns).
  Net of it, at 8 to 128 returns `proof completion` costs 298 to 4,498 units
  (663 to 110,163 before), `contract path preparation` 918 to 13,158 (1,843 to
  96,583), and `proof context finishing` 6,896 to 99,656
  (`early_return_finishing_shares_path_prefixes`, nightly through 64).
  Checking those paths shares what used to be copied per join or per path.
  A terminal join nests its arms' deferred post-execution tactics under one
  node whose arms are shared (`DeferredArm`), not deep copies of every deeper
  join. Its frontier effects start from the arm that appended more and add the
  other arm's suffix, taken by length (`ExecutionFacts::appended_since`)
  without comparing the shared prefix. An outcome goal merges its path's fact
  and effect streams only when read (`OutcomeExecutionFacts`), and a resource
  claim reads them only to describe a failure. A step lists its case facts
  through a membership set and skips facts its context already holds, a
  function's address-taken locals are found once per body, and path synthesis
  checks the finished tree for `ArithmeticUsing` once rather than at every
  nested level. An `ExecutionFacts` stream builds its membership indexes when
  first queried and keeps built ones current as it grows, so a stream
  published per path and never queried indexes nothing. A path's case facts
  stay indexed as they grow and fork; a terminal join answers whether a path
  holds its arm's facts from that index rather than the path's own streams,
  and copies a path's checked leaf only when the arm added a fact or changed
  the candidate it holds; its key for merging duplicate paths orders by
  stream lengths and call routes before states and facts. A
  return appends its trace's effects whole when none can repeat a completed
  fact: effects are certified or memory effects, case facts are neither, and
  only the statement's own facts are looked up
  (`ExecutionProofCore::completed_path_facts_with_effects`). The same
  regression counts outcome merges and arm effect suffixes, which stay at
  zero, and facts indexed from scratch, which stay within the premises the
  path theorems list (completion indexes each path's facts once to list
  them).

Loan-preserving cache havoc uses a maintained interval index keyed by exact
coordinate origins, including symbolic pointer expressions. Unknown relative
bounds forget the cached value; they never authorize a write. The write barrier retains its independent loan checks. Interval queries
ask whether a bucket is nonempty, without enumerating the loans it contains.
`loop_head_havoc_work_over_cells_and_symbolic_loans` enforces near-linear work
as cached cells and unrelated symbolic loans grow together. The write barrier's
symbolic-loan comparison is a separate remaining checking caller; cache
retention evidence must not be used to grant write permission.

Loan write barriers consult the maintained active-memory-loan count before
pointer alias discovery. Empty ledgers, non-memory loans, and ended memory
loans impose no loan restriction on a write; checking them must not visit the
pointer's equality class. The
`writes_without_active_memory_loans_do_not_walk_pointer_aliases` regression
grows that class for constant and symbolic bounds, including repeated checks
and the no-refusal diagnostic path. This shortcut does not replace ownership,
bounds, or definedness checks.

Concrete loan write barriers select one indexed conflict witness instead of
collecting all overlapping loan IDs. Each dyadic bucket contributes only its
least member; taking the minimum across those buckets preserves the diagnostic's
loan choice. Both checking and refusal diagnostics use this selection. The
`write_barrier_does_not_enumerate_overlapping_loans` regression grows overlapping
loans around one fixed write, including covering and adjacent queries and repeats.
Symbolic-loan and alias candidate discovery remain separate checking costs.

The following are known violations of the fast-part rule, listed under
"Fast-part scans" in [the smart-tactics roadmap item](https://github.com/clicklang/click/blob/master/roadmap/smart-tactics.md).
Their mechanisms are described here; their cost is not accepted.

- **Interface-join binding inheritance.** The successor's bindings are
  compared with the arms' through one membership index over binding values,
  linear in the binding count, which grows with proof length
  (`interface_binding_inheritance_is_near_linear_in_the_binding_count`).
- **Uncharged transport contexts.** Explicit transport planning still builds
  contexts through `assume_proposition_uncharged`, counted separately by
  `count_uncharged_context_entries`. It admits the path's memory-effect facts
  and available premises afresh, so that preparation grows with the path.
  Carrying an indexed context with the proof state would avoid rebuilding it.
  This is separate from statement-result publication, which retains producer
  facts and does not construct a bonus-fact transport context.
- **Early-return statement checking.** Under callgrind, checking the
  128-return expansion executes 3.12 billion instructions and the 64-return
  one 1.43 billion (2.2x; 5.85 and 2.07 billion, 2.8x, before the sharing
  above). The rest is per-path or per-step work over the prefix: each step
  still lists every case fact of its path, each return filters its path's
  whole fact and effect history into the candidate's public and memory
  streams, each terminal join visits every path of its arms to record its
  route decision, and completion walks each path's trace from entry. The
  post-execution `have` closers of the claim expansion grow
  `post-execution claim tactics` 2.6x per doubling: each path imports all of
  its store equations.
  Multi-outcome statement producers, summarized loop returns, incompatible
  premise lineages, and legacy producers also keep their ordered path import.

## Execution capacity follows selected syntax

The ordinary kernel execution APIs seed expression and statement capacity with
the evaluator-visible structural cost of the selected C expression, statement,
or function body, plus a whole-function seed's caller-side argument
expressions. This covers one non-amplified traversal of that syntax; it is not
a fixed project-wide source-length cap. A separate fixed reserve pays for
repeated dynamic work: loop iterations, executed callee bodies, short-circuit
or branch amplification. Function-call, loop-unroll, and path-width limits
remain independently enforced. Adding straight-line source increases capacity
only in proportion to that source, while repeatedly executing a small fragment
still reaches a bound. APIs whose names end in `with_budget` preserve the
caller's exact budget and add no source capacity.

## Representation requirements

The complexity contract implies several design constraints:

- Large immutable environments and proof states need persistent structural
  sharing. A clone used to create one modified view is constant or
  logarithmic in the shared structure. Memory states are persistent
  B-trees with cached content hashes ([Memory derivation DAG](memory-dag.md));
  a fact context's stated propositions are a persistent ordered set; a kernel
  statement sequence is a persistent indexed `ProgramStatementSequence` that stands
  for exactly the `Seq(first, rest)` pair tree it replaced; a resource
  context's facts are a hash-consed canonical multiset (`CanonicalFactSet`),
  so equal contexts share one root and compare by pointer.
- Propositions, terms, memories, functions, and environments used as cache
  keys need stable interned identities or cached content fingerprints. Cache
  lookup must not traverse the object whose computation it avoids.
- Fact stores need exact indexes plus theory-specific secondary indexes, so
  condition, quantified, memory/viewability, and resource facts are found
  without scanning all proposition kinds. An expensive key may be deferred to
  its first query when each fact change is still keyed at most once: the
  stated-proposition index records changes on a persistent chain, and a query
  keys only the suffix no earlier query on a shared ancestor built.
- Derived relations such as contradiction, order reachability, resource
  coverage, and separation are maintained incrementally or queried from
  indexed base facts.
- Each function receives the transitive dependencies it references, not a
  copied global environment or every theorem in the project. The parsed
  standard library is shared by every verification in a process and looked up
  through a process-wide name index.

These constraints are semantic-neutral. They must preserve independent kernel
checking and must never turn an unproved, failed, or deadline-limited result
into a cached success.

## Lazy separation and compact composition carriers

Resource contexts never materialize pairwise `ResourceSeparate`
propositions, and neither do the fact contexts that hold them. A multi-owner
context exposes one compact `ResourceComposition` carrier, and holding it
states nothing further (`holding_a_parameter_composition_states_no_pairs`).
A separation query (range and pointer disjointness, subrange inheritance, a
store crossing a cached cell, two distinct range anchors) asks each held
composition for two distinct owned members of the query's block, one holding
each side (`ResourceContext::separated_owned_members_in_block`). Members filed
under the roots the two sides are spelled at are asked first; when they hold
no pair, the conservative candidate index above selects the members. The
answers are exactly those the former pairwise projection gave. A consumer that
needs a separation proposition asks the prover, which serves it from the
carrier on demand and never adds it to ambient fact sets. Borrow/owner
separation over opened composites reads loan bindings indexed by the two
addresses; no tree footprint or list of separated pairs is built.

A verified call's requirement check walks a connective requirement side by
side and does not ask a side its sibling already decides, so a null-guarded
`p == 0 or separate(..)` with `p == 0` asks no separation.

Deciding that a context is a valid partition reads the same indexes: only an
identity held twice or with invalid access, a block owning two or more
ranges, or a base an exact pointer equality joins to another block can hold a
violation. Within one block, an owned range is compared only with the ranges a
fact could relate it to (`ResourceContext::owned_validity_candidates`),
indexed by root: the block and the first symbolic atom of the offset's
canonical form. Validity refuses a proven overlap; it does not prove
disjointness, so two ranges at unrelated roots need no comparison, and every
resource in a composition comes from a transfer rule that never duplicates
ownership (`validity_of_parameter_objects_is_linear`). Rebasing through
aliases asks only alias pairs a constant number of bytes apart
(`footprint_composition_does_not_decide_every_alias_pair`). For constant
intervals, incremental validity selects neighboring owners from the ordered
coordinate index, provided its cached count covers every owner in the queried
block or root. An exact cross-block alias rebases the query before that same
selection; a merely related root must not discard its displacement. This
selection adds no separation facts and still uses the ordinary pair-overlap
rule. Exact-base candidate buckets contain only owners, maintained on
resource insertion and consumption, so unresolved interval checks do not scan
read-only views before checking the owners. Once same-block neighbors
have been checked, the cached number of owned blocks can prove there are no
owners elsewhere. That case skips cross-block alias discovery entirely,
regardless of how many aliases the fact context holds. Pair-overlap checks
also compare exact constant byte coordinates before constructing alias lists.
The same coordinate rule handles translated bases, mixed element widths,
and narrow or native bounds. Explicit-separation queries use it to reject
literal overlap without alias discovery; a separation certificate cannot undo
that overlap. Unknown bounds or different origins still require other reasoning. Symbolic bounds, incompletely indexed roots, and other related bases
still enumerate candidates: a known violation of the fast-part rule
(see "Fast-part scans" in
[the smart-tactics roadmap item](https://github.com/clicklang/click/blob/master/roadmap/smart-tactics.md)).

Negative memos over memory-DAG walks key on the derivation generation, which
advances only when an earlier state receives its edge
(`recording_a_fresh_state_keeps_the_derivation_generation`).

Terms have one canonical identity and state changes are explicit:

- **Stratified derivation edges.** A state's derivation is described in
  its parent's vocabulary; call-havoc footprints are recorded in
  assumption-free canonical form. A frame proof needing another vocabulary
  supplies an explicit `frame using` restatement.
- **Canonicalize at creation.** A memory load becomes the load variable for
  its cell version where lowering or execution creates it, so condition-fact
  availability is exact canonical-form lookup. Separation facts use a
  state-independent shape index only to select candidates; the kernel then
  proves the range relationship from frame evidence. See
  [Canonicalization](canonicalization.md).
- **Transport facts at statement boundaries.** A statement step carries only
  facts whose direct frame check succeeds; other cross-state reasoning is
  an explicit `transport`, not a comparator side effect.
- **Rewrite states by identity.** Substituting a variable visits each
  interned state once; memoizations are pure functions over interned ids.
- **A search attempt asks each failed question once.** Inside one attempt
  (`with_closure_failure_memo`) a failed reachability, load-bridge, or
  pointer-distinctness check is remembered by its exact inputs, fact-set
  content id, DAG generation, scope modes, and in-progress lookups. Failures
  that met a cycle cut or limit are not kept, and nothing outlives the
  attempt (`closure_failure_memo_answers_a_repeated_failure_once`). An
  explicit `transport` opens the same scope.
- **Select pointer rewrites from the differing offsets.** A same-block
  pointer comparison selects facts about the differing offsets only; literal
  values never nominate rewrite candidates.
- **Decide an overlap before searching for a separation.** A cell a callee's
  write set contains through one alias and a constant displacement is decided
  before any separation search runs.
- **Explicit proof steps remain the completeness escape hatch.** `rewrite`
  uses a proved equality and `transport` uses checked frame evidence; the
  canonical comparator uses neither.

## Indexed contradiction and premise search

Derived contradiction checking and condition premise search follow one
pattern: per-term facts fold into indexes once, and pairwise proof work runs
only where a theory rule's own first-line requirements say a pair could
relate.

Context inconsistency is indexed as facts are assumed
(`src/kernel/assumptions/contradictions.rs`). Each condition fact files under
the keys its rules read: its canonical condition with its polarity, its
order edge between two equality classes, and its variable's constant bounds
and excluded values. The classes are a union-find over context-free
order-endpoint keys (constants folded, addends sorted, loads in their
context-free form), joined by the context's equalities; a merge moves the
smaller class's edges. `is_inconsistent` reads whether any key is in
conflict, so it costs nothing per fact
(`one_added_fact_and_the_query_cost_the_same_beside_any_number_of_facts`).
Assuming the opposite truth value of an exact held condition preserves the
condition and its indexes and directly records `false` in the proposition fact
set. `is_inconsistent` reads that exact fact before consulting derived indexes.
The false fact has ordinary proof syntax and survives premise reconstruction;
explicitly restricting away that fact removes its authority. The regression
`contradictory_branch_creation_does_not_rebuild_ambient_indexes` measures repeated
contradictory branches beside 32, 128 and 512 unrelated facts. Contexts only
grow and fork: a branch retains its parent context, so no fact is ever
withdrawn from these indexes.
Nothing else is compared:
two endpoints that only memory resolution, the add rule, or another theory
rule could equate are not related, and neither is an alias guard to a
separation or a pointer disequality to the congruence closure. Those
contradictions are left to proof steps.

A condition-fact query (`PureFactContext::has_condition_fact`) reads the
facts filed under the keys it spells: its kind and the canonical forms of its
two sides and their recorded-equality classes. A fact of two atoms is never
visited by a query that does not spell its key
(`condition_fact_queries_ignore_unrelated_facts`). A fact with a non-atom side
(a load, a sum, a conditional) can match through reasoning its key does not
spell. When the keys miss, the query reads the facts filed under its own
variables and the members of their recorded-equality classes
(`condition_facts_by_variable`), never every fact of its kind
(`open_sided_condition_queries_read_only_their_variables_facts`). A ground
fact that matches only through a known constructor, or a load variable that
equals another only by memory resolution, is not found this way.

Order questions inside the decision and inside memory resolution (whether
one index is below another, so two cells of one array are distinct) are
answered by the difference graph (`difference_graph_proves_order` in
`src/kernel/assumptions/condition_reasoning/order_paths.rs`), which is updated
per fact and follows at most `EDGE_LIMIT` edges per query. An order chain
longer than that is left undecided; a proof states an intermediate bound. The
bound searches (`has_lower_bound_*` and `has_upper_bound_*` in `bounds.rs`)
read a term's bounds from `signed_order_bounds`. The outermost search judges
each bound with one nested decision, and a search inside that decision uses
constants, exact facts, and the graph only, so a search never follows a chain
of bounds.

A term's constant after equality normalization is a lookup in the equality
graph's scalar classes (`EqualityGraph::scalar_constant_class` in
`src/kernel/equality_graph.rs`; see [Equality closure](equality-closure.md)).
Each class carries the merge of its members' folded constants, a union merges
two classes' constants, and a class whose constant rises re-folds only the
compound terms that use one of its members; a constant only rises, so each
term is re-folded a bounded number of times along a path. Signed byte reads
of byte loads are kept per class and inverted into the byte's class on a rise
([byte representation](byte-representation.md#character-reads-of-one-byte-cells)).
Only a class without a settled constant resolves its conditional members at
query time; unregistered arithmetic folds from its operands. Constant lookup
never pairs loads from different states or searches memory history for a
constant. Missing relations must already be established in the equality
context. `constant_queries_ignore_other_state_candidates` covers misses,
explicit-equality hits and repeated queries as related and unrelated state
reads grow; `counter_call_chain_ensure_lowering_stays_flat_per_call` covers
repeated calls.

The condition-premise oracle follows a persistent variable-to-fact adjacency
index; each reachable variable and fact is expanded once
(`connected_condition_selection_scales_linearly_in_chain_and_context`).
Memory state-dependent facts can connect to a goal through a variable stored in
their state, so their entries are deferred until queried and cached after a
complete construction. The first query pays for every pending state fact
of the bucket, a known violation of the fast-part rule.

Condition premise search tries single candidates, then candidate pairs that
some derivation could connect: two facts sharing a bitvector variable, or two
facts each sharing one with the goal. A pair sharing neither holds no
derivation the single pass misses. Wider premise sets come from one
derivation over the candidate set minimized to its dependencies. Quantified
matching is a per-query linear scan over quantified facts, a known violation
of the fast-part rule (possibly better made expandable, since choosing an
instance is a search).

## Condition decisions in simple checking

The kernel's own condition evaluation (`decide_with_facts`, the path-fact
consistency check, a merged branch's path facts, a loop condition) does not
search the path. It reads exact facts, the condition's own form, and the
context's `DifferenceGraph` (`src/kernel/difference_graph.rs`) with its keyed
rules (`PureFactContext::difference_decision`). A condition the fast path
leaves open keeps both branches, and a requirement it leaves open needs a
proof step that states it.

The general decision `PureFactContext::decide` is also fast-part checking,
not search: it selects no premises and tries no alternative rules, and simple
tactics use it to check a premise (`holds_by_lookup_or_decision`, used by
`fold`, resource steps, and step certification). Its nested rules can reach
far: a memory read compares states, and one decision asks others. Each outermost decision runs under a fixed per-query
fuel, `DECISION_FUEL_LIMIT` (`with_decision_fuel` in `src/instrumentation.rs`);
every charged unit spends fuel. A decision that
exhausts its fuel ends undecided, no memo keeps the answer, and no budget
fails. The fuel is a safety net against a runaway decision, not a license to
scan; the decision's remaining scans are listed under "Fast-part scans" in
[the smart-tactics roadmap item](https://github.com/clicklang/click/blob/master/roadmap/smart-tactics.md).

The graph's nodes are `int32`, `uint32`, `int64` and `uint64` values keyed by
term, and its edges are constraints `x - y <= c`; a constant bound is an edge to
a zero node, so facts about unrelated values never meet at a shared constant.
A word's `uint32` node is paired with its `int32` node, and the pair is linked
once either interval settles the word's sign, a constant-size step per
tightening (`unsigned_work_is_flat_beside_values_bounded_by_its_hub`).
Insertion propagates bounds and checks for cycles along at most `EDGE_LIMIT`
edges, and a read pulls one hop from a node whose push was cut short, so a
value many others are bounded by costs the same however many there are. Past
the limit the graph answers less, never something false. Order queries first
look up the edge by its two endpoints, so a written `ck < n` stays usable when
`n` bounds many unrelated indices. Pointer classes and disequalities, known
low bits, and no-overflow facts are keyed by their own values. The same field
of two bases asks the bases' own offset question, one recursion per field.
`work_is_independent_of_unrelated_bounded_values` pins insertion and query
work, and `decisions_hold_in_every_model_and_are_complete` checks each answer
against every model of generated fact sets.

After checking each `int32` addition's overflow guard, execution combines a
trailing constant offset with the next constant when the sum fits, so a chain
of increments stays shallow and later overflow decisions do not walk every
earlier increment (`signed_increment_overflow_checks_stay_flat_per_assignment`).

The graph decides difference constraints only. Non-linear arithmetic,
relations between sums of variables, and an overflow bound resting on a guard
over a sum (`a <= INT_MAX - b`) are out of its reach. Simple checking does not
rediscover such a bound; a proof states it with a lemma. The implicit closer is not
promised to close what the fast path leaves open.

## Termination heights and local descent

Whole-project termination is decided in two passes over one call graph, built
once from the run's verified functions and the contract-less `static inline`
helpers they reach. That forward call closure is the one termination cost
that is not per-function local, and it is charged to visible input and
output: the closure is the selected syntax, and a height for each node is the
planner's whole result. For a function with complete checked execution
evidence, call dependencies come from its retained checked statements,
collected once when the execution artifact is finalized and shared by
identity across claims (`checked_callee_summary_reuse_scales_with_input_not_product`).
A branch proved unreachable adds no calls; a summarized statement adds every
call in its syntax; missing evidence falls back to the source body.

`program_termination_height_plan` proposes a height per node (iterative Tarjan,
longest path over the condensation, cycle members sharing a height).
`program_verified_function_termination_rules` checks the proposal level by level in
ascending height, reading at each call site only whether the callee is above
its caller, whether a strictly lower callee has evidence, and whether an
equal-height callee is a recursive edge a declared measure ranks. A refused
member withdraws its same-level callers through a worklist that pops each
refusal once. Function-pointer calls add one body walk for taken addresses
and at most one more settling pass.

The work is linear in the call graph's nodes and edges, up to the indexing
factor of name-keyed BTree containers. Neither pass performs a reachability
search, and the plan is untrusted: a wrong height can only refuse a function,
never certify one. The scaling tests in
`src/scaling_tests/kernel/termination/termination_scaling_tests.rs` pin five
graph shapes at 500 to 4,000 functions, asserting the verdicts at each size
and counting cooperative checkpoints rather than host time.

## Checked execution reuse

Select the function-proof driver before executing a wholly linear script;
running a complete prefix merely to decline and repeat it in another driver
multiplies all statement and tactic work.

Ordered finalization and opaque-contract certification share function-body
work only through `CheckedFunctionExecution`, a kernel-created artifact
retaining the exact entry state, annotated function, arguments, environment,
execution semantics, loop judgment, assumptions, and complete checked
frontier. Its fields are private to the kernel; a planner can retain the
artifact but cannot manufacture its authority. At the opaque-contract
boundary, the kernel reconstructs contract assumptions and resource-guard
cases independently and reuses an artifact only when all retained structural
inputs and policy flags match and every retained premise is proved by the
reconstructed context. A limited or empty frontier is never reusable, and
certification never executes the body. A set of paths is prepared for claim
checking only when a claim is judged over it.

Proof-directed folds, unfolds, and observations are retained as checked
zero-source execution events naming their input state, definition, and output
delta, so completion follows the event without interpreting the C body again.
Each reused artifact must cover the whole entry on its own; artifacts checked
under opposite cases of an entry condition are not composed. Grouped claims
retain the same artifact, so adding claims does not multiply whole-function
execution.

## Sequential loop clauses

A `loop` tactic at the k-th of N sequential loops pays for its own loop:

- The path's facts are a persistent `PureFactList` with indexes of exact
  facts, conjuncts, and transport candidates; the next `loop` extends the
  list its predecessor copied by the facts gained since. Unfolded predicates
  retain both their opaque atom and definition at loop entry; deleting the
  atom would invalidate the shared reasoning context and force a rebuild.
- Fresh-identity reservations are `LazyReservedVariables`, answering
  execution-range candidates above the context's ceiling without collecting
  variables. Loop rules are a persistent `VerifiedLoopRules` indexed by a
  fingerprint of their loop statement.
- Applying a loop rule under the context it was certified under compares fact
  sets by identity (`PureFactContext::holds_the_facts_of`).
- The function is annotated by one whole-function walk per claim; a later
  loop lowers only itself from the recorded walk state when its block differs
  only by that loop's clause.
- Structural clauses are a persistent `StructuralClauses` indexed by loop and
  label, so binding a clause and finding a loop's clause cost the clause.
- A lowered loop is put in place by following its path from the body's root
  (`KernelLoopPaths`) through `ProgramStatementSequence`, logarithmic in the block
  (`putting_a_lowered_loop_in_place_reads_its_path_not_the_loops_before_it`).

`sequential_loops_build_the_same_context_entries_each` requires the same
counts of context entries, fact copies, index entries, reservations, and
annotation walks for each further loop. The debug cross-checks
`CLICK_DEBUG_CHECK_FACT_LISTS=1`, `CLICK_DEBUG_CHECK_LAZY_RESERVATIONS=1` and
`CLICK_DEBUG_CHECK_LOOP_ANNOTATIONS=1` compare each indexed answer with the
walk it replaces.

## Atomic source selection

Atomic memory and resource source selection uses the kernel's candidate
indexes. Viewability queries select address shapes from structural anchors and
known aliases; a singleton selected view can cover a displaced address. They do
not enumerate all other ranges in the block. Adjacent-view checks select a
suffix at the prefix's endpoint, including an exactly addressed materialized
cell or dense run span ending at its next hole, instead of pairing ambient
ranges or enumerating memory cells and runs.
Candidate states, extents and pointer equality still pass the kernel checks.
Read-defined goals use typed evidence, exact aliases and equality spellings;
memory separation uses the unordered block-pair bucket. Large buckets at the
same address and long alias components still need separate growth audits.

Atom memory-condition matching uses exact/canonical condition keys and keys
from equality spellings. A miss does not consult the family's entire open-fact
bucket. A condition requiring a different spelling can be established explicitly
before the checked operation. Compound-query and carrier/state controls remain.

Atomic certificate planning keeps persistent syntax adjacency for condition
and proposition facts, keyed by value variables and explicit pointer blocks;
filing a fact adjusts only its keys. Each complete fact is
shared across its buckets, so a wide premise costs its syntax once
(`wide_atomic_premise_cloning_scales_with_its_syntax`). Candidate trials check
named sources alone first, then walk only condition buckets connected to the
goal and source. Wider smart fallbacks belong to the slow part and are charged
to its budget; every successful selection still establishes the goal in the
restricted kernel context.

Before spelling a typed equality, `solve` retains only the sources its
evidence named, and the kernel rebuilds the selected context from them.
Compatibility evidence that retains a whole connected component can be
reduced by bounded chunk-deletion trials (at most 255 restricted queries,
charged to the smart budget). Theorem application retrieves the latest
recorded source form of its exact matched premise from `SurfacePropositionMap`,
following one selected fact. A read of a held native range uses the address
graph's retained wide-index producer rather than a narrow alias's spelling.

## Regression policy

Wall-clock examples find user-visible pain, but they do not enforce a scaling
law. Performance-sensitive changes need deterministic scaling regressions that
generate at least four sizes, normally `N`, `2N`, `4N`, and `8N`, and measure
verifier work rather than host time. Each sample records work attributed to
named verifier operations and tactic kinds, and a failed curve reports those
named curves; wall-clock profiler attribution is corroboration. Exact
repeated-sample comparisons measure the named operation itself
(`choose_projection_walk_is_deterministic_across_selected_body_sizes`).

The scaling suite covers independent axes:

- number of unrelated functions and verified rules;
- straight-line statements and program-point states in one function;
- ambient pure and condition facts;
- surface-to-kernel proposition spellings;
- resource facts and resource-definition members;
- global and imported theorem declarations;
- number of claims sharing one function execution; and
- call-graph nodes and edges in whole-project termination checking.

A fast-part regression grows both unrelated input (more facts about other
values) and related input (a longer chain of facts about the same value), as
the [design check](verifier-design.md#design-check) requires. One operation's
work must stay flat, up to polylog factors, as unrelated input grows; linear
growth with unrelated context is a violation of the fast-part rule, not a
pass. For a linear or `N log N` path in related input, doubling the input
stays close to a factor of two after fixed startup work is excluded. A
regression must fail on the old representation and pass on the new one.
Absolute corpus timings are corroboration, not a substitute for the scaling
assertion.

Any new hot-path collection, cache, or clone answers these review questions:

1. What is its size in terms of source or explicit-proof input?
2. Is lookup indexed by the exact semantic key?
3. Does mutation share unchanged structure?
4. Can one operation enumerate unrelated entries?
5. What scaling regression protects the claimed bound?

See [Testing Click](testing.md) for commands, budgets, and profiling. The open
implementation work is ordered in
[`roadmap/README.md`](https://github.com/clicklang/click/blob/master/roadmap/README.md).

### Theorem operation discovery boundary

Named theorem application has three primitive phases: prepare the selected
arguments and instantiated conclusions while returning prerequisite obligations;
prove those obligations in the driver with ordinary solve; publish the retained
conclusions. Pure, fixed-state, live and returned-outcome applications share this
route, including the population-member-count-zero and Integer range-fold
built-ins. Explicit `apply(...) using { ... }` is the replay operation.

In test builds, `FastOperationScope` surrounds preparation, publication and
explicit theorem application, contract-claim opening, and proposition/resource
scope completion. Claim opening retains its goal without proving separation;
its explicit proof can apply the exact live-partition rule through `known()`.
Prepared statement/fold publication is guarded independently of obligation
solving. Every `ProofSearch` method records entry before
any work, including exact-fact shortcuts; constructing `SearchPermission` also
records discovery. A search entry inside a guarded primitive panics, including
when the primitive itself was called by search. Driver obligation solving runs
outside the primitive scope. Nested scopes and unwinding restore the previous
scope. The build boundary requires both the search-entry instrumentation and the
migrated operation scopes.

Generic declarations are proved at arbitrary rigid types before use. Application
instantiates their statements without traversing proof bodies or re-running
verification; there is no cold-instance proof cache or discovery-guard exception.
The type-specific `separation::separate_elements` and `separation::distinct_elements`
laws retain explicit checks for their supported index types. Generic separation
laws also retain the nonzero storage-width requirement. Declaration verification
still instantiates proofs where required. `cold_theorem_application_ignores_declaration_proof_length`
measures first and repeated explicit applications at growing declaration-proof
lengths; the statement-instantiation regression also excludes proof locations.

This is a discovery boundary, not a complexity proof: it does not detect an
unregistered helper's loop, a scan in lowering, or expensive fact admission.
Those still require the operation audit and deterministic scaling regressions.
