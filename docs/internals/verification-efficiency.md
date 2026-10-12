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

Trace source locations follow the same rule. Resolve a claim's written tactic
locations together and reuse that result for every step, including missing
indices. Computing their line and character columns uses one source walk;
reparsing the project or rescanning a long line for each location is not
acceptable. The CLI cache and batch-position regressions cover 16, 64, and
256 locations.

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
verifier, and the complexity contract above applies.

Report both numbers when delivering an example. As of 2026-10-07,
`examples/rbtree-insert` is about 2,500 proof lines for 136 lines of C, 19
times, and verifies in about 5.4 seconds, roughly 470 lines per second.

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

Logical reads through opaque pointers select an admitted footprint's address
coordinates through the composition's existing class and interval indexes.
Only producer-published footprints enter this selection index; admitting raw
composition provenance still shares its persistent storage without a scan.
Admitting a composition or pointer equality advances only its prepared index
delta at that producer. Selection aligns one supplier occurrence against the
trusted graph; it does not enumerate pointer spellings, scan composition
frames, or resolve older snapshots. Address alignment grants no read authority
or value preservation. The regression
`logical_read_address_uses_class_index_without_scanning_aliases_or_frames`
varies unrelated compositions and equivalent pointer spellings at 4, 64,
and 1,024 entries, including field offsets zero, four, and eight.

## Output-sensitive exceptions

Some verification work is inherently larger than one lookup. Its cost must be
charged to visible semantic output rather than hidden ambient state:

- A source branch can create two paths. Repeated branching may create many
  paths, but verification should share common prefixes and cost no more than
  the explicit path structure it checks.
  Path certificate merging advances borrowed cursors through checked steps
  and case offsets, then builds control nodes from checked children. It
  charges prefix comparisons, copied steps, and case traversal; it does not
  convert or revalidate every remaining subtree at each case level. The
  `path_certificate_merge_work_is_bounded_by_its_input_steps` regression
  bounds this work by the supplied steps and cases at 4, 64, and 1,024 leaves
  and checks that selecting every merged leaf recovers its original proof.
  Checked loop exits share immutable fact lists when copied into the loop
  rule; construction charges each fact and the rule charges each copied exit
  handle. `checked_loop_exit_copies_share_their_fact_storage` checks both
  exit forms at 4, 64, and 1,024 facts, alongside the full loop-exit scaling
  regression.
- A loop exit join reconciles contract-call epochs through changed marker
  entries, retaining common history and one fresh marker. It does not union
  every branch's epoch into a successor that every exit must then scan. The
  deterministic kernel regression measures 72, 780, and 12,300 work units
  for 4, 64, and 1,024 exits, including all residual checks, and varies
  unrelated cached cells independently. Checked load equations are consulted
  only for changed concrete cells, using a load already named at the exact
  snapshot and address and indexed equality evidence. A missing name declines
  the optional cache reconciliation; it never walks unrelated store history
  to construct one. Each exit's fact context is built lazily once. Compact
  cached runs are not enumerated by this reconciliation.
- A contract-less inline helper never symbolically expands an undecidable
  loop guard into continuing iterations. It returns a local refusal at that
  guard, so accumulated histories cannot grow with the unroll allowance.
  `symbolic_inline_loop_refusal_work_is_independent_of_unroll_allowance`
  checks 30 deterministic work units at allowances of 4, 64, and 1,024, exactly
  one consumed iteration, and one diagnostic path. Concrete unrolling and
  restoration of the enclosing call context on errors are checked separately.
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
- An explicit quantified frame (`src/kernel/quantified_frame.rs`) walks the
  source and target once in parallel, renames each universal binder once,
  and asks the kernel's existing checked load-history question once per
  differing read; it indexes the context and never instantiates a
  quantifier. Its single-fact fallback reads the single-fact route's own
  premises rather than the whole context, since that route's cost grows with
  the facts it is handed. It runs only where the single-fact transport
  refused, so a transport that route already carried costs what it did, and
  a smart closure answers a repeated failing frame from its failure memo. The surface
  regressions `quantified_frame_is_near_linear_in_crossed_stores`,
  `quantified_frame_is_near_linear_in_its_body` and
  `quantified_frame_is_near_linear_in_unrelated_facts` pin the frame's named
  work at 255 to 1,963 units for 4 to 32 crossed stores, 151 to 319 for 4 to
  32 framed conjuncts, and a flat 133 for 4 to 32 unrelated requirements. The
  store axis asserts the whole verification as well, since a store's
  refusal to keep a cell it may alias reads only filed order facts (see
  [Indexed contradiction and premise search](#indexed-contradiction-and-premise-search)).
- A store keeps every earlier cell of its block that it proves it misses,
  and outside one case it still decides each one: the cell map offers no way
  to keep a group of cells without asking each, so a straight line of `N`
  stores to cells the facts keep apart asks `N^2/2` cell questions. The one
  case is the constant byte gap (`src/kernel/reasoning/store_gap.rs`). A
  cell at `S + c` beside a store at `S + k`, for one symbolic anchor `S`
  (or two constant offsets), is decided by `c - k` alone, and `Pointer`
  orders every `S + c` of one anchor as one key range by `c`, so the store
  keeps the cells whose windows its bytes clear without visiting them and
  asks only the cells within eight bytes of its own and those at other
  spellings. The ranges name only shapes whose ladder answer is "keep" by
  structural cancellation and constant arithmetic, reading no fact, and
  they are empty while implicit provenance is captured or after the
  deadline; debug builds re-ask the ladder about the cells at each end of
  every range, and `skipping_constant_gap_cells_leaves_every_store_unchanged`
  compares generated store sequences both ways, forget marks included. A
  line of constant-index stores (`a[0] = …; a[1] = …`) costs 477 to 11,339
  units of store work at 4 to 64 stores in a debug build (467 to 8,959 in
  release), where it cost 445 to 46,017
  (`stores_to_constant_indices_are_near_linear`). Symbolic indices are
  still asked cell by cell, so that line is still `N^2/2` questions, but a
  question no longer walks its own order path: when only a chain of order
  facts separates the cells (`c0 < c1 < …`), each walk used to climb the
  chain between its two indices and the line cost `N^3` (830 to 1,032,462).
  The order walk now shares reachability across walks toward one target
  (`OrderReachMemo` in
  `src/kernel/assumptions/condition_reasoning/order_paths.rs`): a success
  files the states on its path, a complete refusal every state it reached,
  and only over terms that read no memory, where each test the walk applies
  is a question about the fact set alone. The line now costs 738 to 123,290
  in order and 900 to 149,372 in reverse order
  (`stores_to_chain_ordered_indices_are_quadratic_not_cubic`, pinned below
  the cubic curve), and
  `memory_resolution_order_walk_memo_agrees_with_the_full_scan` compares the
  memoized walk with the full scan on generated fact sets. The `N^2/2`
  questions for symbolic indices remain a known violation of the contract;
  removing them needs the cells indexed by the index terms the facts order,
  which no rule has yet. Union views are still visited per candidate on
  every store. The initialization record (`InitializedBytes` in
  `src/kernel/primitives/initialized_bytes.rs`) is not visited by a store:
  a store only adds to it, merging constant-offset bytes into one run per
  block with a predecessor lookup, and a forgotten cell's bytes are recorded
  at the cost of the forgetting itself
  (`an_unplaced_store_records_a_local_array_as_one_run`). A run of cells a
  havoc or store drops as a whole is recorded per dropped interval, not per
  slot: a declaration's initializer records its whole object, so dropping
  the runs it seeded is one covering query each, whatever their length
  (`a_declared_object_makes_dropping_its_runs_one_query`).
  A symbolic store invalidates a compact constant-value run by its possible index window,
  or forgets the whole run when the index is unplaced. It keeps values outside
  a proven window and records dropped initialized bytes per interval; it does
  not ask every logical element for extra separation facts. The regression
  `symbolic_stores_into_compact_arrays_scale_with_represented_cells` measures
  bounded and unbounded stores at 4, 1,024, and 1,000,000 elements. A constant
  store checks partial coverage at live-interval endpoints, also charging the
  intervals rather than walking all overwritten slots.
- Every fact a context is built from is charged one unit of deterministic
  work (`PureFactContext::assume_proposition` and `assume_condition`), so a
  context rebuilt from a growing list at each step shows as quadratic work
  instead of hiding in wall time. A path's facts carry the contexts they
  build: planning keeps them in a `PureFactList`, and the certificate facts'
  store keeps its own, each extended by the facts a step adds and rebuilt
  only when a step removes or reorders a fact inside the built prefix. Claim
  setup and whole-function finalization build the entry facts' context once
  and extend it per path, and the implicit empty-effect check builds a
  path's context only when a write could reach storage that predates the
  call. `executing_a_fan_out_is_near_linear_in_its_length` pins `execute()`
  on an early-return fan-out, where it builds no path context of its own,
  and
  `call_ensure_lowering_is_linear_in_the_ensure_count` and
  `call_requirement_checking_is_linear_in_the_requirement_count` pin the
  builds of a call step (`context_rebuild_entries`).

  Simple loop-invariant checking also carries a prepared persistent path
  context between declarations. Canonical merges report appended members and
  complete source-metadata replacements; the context and collected bundle
  receive only that delta. Mandatory verification conditions remain unassumed.
  `invariant_back_edge_context_extension_scales_with_members_not_ambient_facts`
  checks declaration growth independently of unrelated ambient facts, and
  `prepared_path_extensions_with_new_facts_and_obligations_build_only_the_delta`
  checks a new fact and obligation at every step against a fresh context.

  Three builds remain charged nothing (`assume_proposition_uncharged`,
  counted by `count_uncharged_context_entries`), each a known violation. A
  step's direct-transport context covers its statement-local facts, and a
  simple step's statement-local facts hold every observable resource fact
  of its state, so the context is linear in the unrelated resources at each
  call step: charging it grows
  `expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations`
  a unit per unrelated allocation. An explicit `transport` assumes the
  path's memory-effect facts and every available fact afresh, so each transport is
  linear in the path: charging it pushes
  `expanded_roundtrip_work_per_source_byte_is_logarithmic` past its bound.
  The set of a path's retained facts that evidence checking reads once per
  checked step (`proof_evidence_unretained_premise`) is not a context, but
  it is the same kind of rebuild: charging it grows the expanded extra copy
  a unit per unrelated allocation. Removing them needs the resource facts'
  and the path's memory-effect facts' contexts carried with the proof state.

  Completed early-return paths retain shared fact prefixes and immutable
  candidate records. Terminal joins concatenate persistent candidate,
  evidence, and provenance vectors instead of copying the returned paths at
  every enclosing join. Balanced concatenation joins immutable child nodes
  without copying either sibling's records. Exact execution-fact membership uses
  a persistent hash index that includes certification and transport metadata.
  Its regression counts actual fact-iterator reads and requires none for indexed
  membership across 64 through 512 facts. Legacy traversal accounting described
  above remains unchanged.

  A checked single-outcome statement also retains its typed proof-fact
  context. Outcome goals reuse it only for the identical candidate record
  and a compatible entry-fact lineage. They compute the frontier's new
  ambient suffix once, reject incompatible leaves, and import local effect
  evidence rather than rereading every enclosing guard. A terminal join may
  preserve this cache after checking an arm's introduction delta and
  republishing that exact record. Statement premise checking shares the current
  effect history instead of rebuilding a deduplicated stream eagerly. Post-execution case routing retains unchanged
  records and extends each cached context with its checked case delta. Duplicate
  statement premises retain their
  original priority without being reported as new introductions. Statement
  priority batches retain the identical checked case-prefix stream and store
  only their local suffix, so cached leaf contexts do not introduce a new
  flat array of guards per return. Statements selecting a different ordered
  batch keep their exact input; the regression bounds total retained entries
  and the number of materialized multi-fact batches.

  `completed_early_return_contexts_are_reused_for_certification` measures both
  grouped and explicit proofs at 4, 8, 16, 32, and 64 returns. It bounds whole
  work, context construction, retained fact objects and chunks, terminal
  publication visits, and logical outcome imports. At those sizes, imports
  are 10, 18, 34, 66, and 130 in both forms; all returned leaves reuse their
  checked contexts. The vector regression counts payload copies through
  1,024 records in both concatenation directions, and bounds node work for
  repeated 128-record sibling blocks. Indexed edits preserve other forks and
  their cached slice views. Branch regressions check
  opposite-arm isolation, added ambient premises, and cache invalidation by
  candidate identity; false-final-path fixtures remain rejected.

  Multi-outcome statement producers, summarized loop returns, incompatible
  premise lineages, and legacy producers keep their ordered path import.
  Entry-resource propositions still require the existing certification
  merge when their precedence matters. Those fallback checks preserve
  authority and ordering; shared storage does not grant a theorem or bypass
  independent execution-trace and contract certification.

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
- The parsed standard library is shared by every verification in a process.
  Validation borrows its theorem declarations and a theorem environment looks
  them up through a process-wide name index, so a verification copies only
  its own file's theorems; `verification_copies_only_its_own_theorem_declarations`
  (`src/surface/tests/scaling_tests.rs`) counts the copies at 4, 8, 16, and
  32 file theorems.

These constraints are semantic-neutral. They must preserve independent kernel
checking and must never turn an unproved, failed, or deadline-limited result
into a cached success.

## Lazy separation and compact composition carriers

Borrow/owner separation over explicitly opened composites uses existing checked
loan bindings. Composition admission indexes only changed memory-address keys
and changed bindings; a persistent binding journal also captures changes that
leave the resource store itself unchanged. Queries consult sources indexed by
the two addresses, and recheck the exact retained composition. They do not scan
unrelated resources or unrelated composition history. Repeated bindings share
their existing state. No complete tree footprint or list of separated pairs is
constructed. The `borrow_partition_tests` regressions check evidence withdrawal,
overlap rejection, branch-local binding changes, and lookup/admission scaling
with growing unrelated state. The surface regression
`composite_borrow_partition_nested_openings_scale_with_depth` checks explicit
nesting at several depths. Exit resource equality tries the requested
fold/unfold comparison by consumption before searching combinations of exposed
definitions, and exposure stops when a non-memory target is found.

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
- **A transport attempt asks each failed question once.** A `simp` attempt
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
  (tested directly by `closure_failure_memo_answers_a_repeated_failure_once`).
  An explicit `transport` also opens this scope: its bridge, reachability, and quantified-frame routes
  can repeat the same failed memory question even without smart search. Nested
  checks share the enclosing scope; standalone checks discard it on return.
  `explicit_transport_failure_is_prompt.md` pins the local refusal below the
  repeated work, and `explicit_frame_refusal_scales_with_unrelated_facts`
  grows independent scalar premises without granting the missing frame.
- **Keep fallback candidates finite.** An indexed equality-rewrite candidate
  may unfold a function and descend through logical structure, but that descent
  cannot restart an equality-rewrite or function-unfold fallback already active
  on the candidate. The outer search retains its equality chain and closing
  probes. Implications and universals run these fallbacks on their introduced
  bodies. Candidate scopes restore on both misses and errors, so later goals
  get their own search. False list-position claims are checked below the
  ordinary smart budget, beside increasing unrelated fact sets and against
  the unchanged `rb_next` proof.
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

The memory-resolution order walk
(`has_order_path_for_memory_resolution`), which proves the index orders
that separate two cells of one array, reads the same way. It used to
compare every node it reached with every order fact and every condition
fact, so a failing distinctness question cost the whole context; a store to
`a[c]` beside other indices bounded by `0 <= ci < n` refused `c < ci` by
reaching `n` and scanning all `2N` bounds, and `N` such stores were
quadratic. Each fact set now files its order edges once, by lower endpoint,
and its true equalities by side (`OrderWalkIndex` in
`src/kernel/assumptions/condition_reasoning/order_paths.rs`). A node that
is a constant or a variable that cannot name a load reads the edges filed
under itself and its recorded-equality class, the edges under its exact
constant, and, for a written constant, the edges from larger written
constants and from endpoints an offset equality scales. Those are all the
routes the walk's unchanged edge test has between two such terms; every
other lower endpoint (a load, a sum) is read at every node, and a node
that is itself a load, a sum, or a variable an offset equality scales
reads every fact as before. So the answers are unchanged
(`memory_resolution_order_walk_agrees_with_the_full_scan` compares the two
walks), and a refusal beside 64 to 512 other bounded indices costs a flat
27 units against 932 to 7,204 for the full scan
(`memory_resolution_order_walk_ignores_shared_bounds_of_other_indices`).
A line of 4 to 64 such stores costs 990 to 18,570 units of store work,
where it cost 2,294 to 408,974
(`stores_to_bounded_unordered_indices_are_near_linear` in
`src/surface/tests/scaling_tests.rs`).

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

The complete condition-premise test oracle follows a persistent variable-to-fact
adjacency index. Facts whose variables can be read without inspecting a
snapshot update the index as they are filed or withdrawn. The context-entry
charge covers the first variable entry; additional variables are charged
separately, and a restriction rebuild pays its own entry charge. Construction
is attributed to `condition variable indexing`, and worklist traversal to
`condition premise selection`. Each reachable variable and fact is expanded
once, preserving fact-index order for the unchanged kernel checker.

Snapshot-dependent facts need the complete collector: a condition can connect
to a goal through a variable stored in its snapshot even when their written
syntax shares none. The oracle defers their variable entries until queried,
charged as `snapshot condition premise indexing`, and cached only after a
complete construction. Scalar changes share this cache; snapshot-fact changes
extend the last completed index with a deferred insertion or withdrawal,
rather than re-indexing older facts. The first query pays for the pending
snapshot facts and their variables, so this fallback remains linear in that
bucket's collected entries. It never walks the complete context per chain
link, and ordinary fact insertion never scans snapshot contents.

`connected_condition_selection_scales_linearly_in_chain_and_context` pins
selection at 39, 79, 159, and 319 work units for descending chains of 8, 16,
32, and 64 links; complete atomic derivation costs 86, 174, 350, and 702.
An eight-link chain stays at 39/86 units beside 32 to 256 unrelated facts.
The former scan, retained as a test oracle, visits 360 to 20,800 facts on the
growing-chain axis. `snapshot_condition_index_builds_once_and_survives_scalar_updates`
pins cold construction at 57 to 169 units over 8 to 64 unrelated snapshot
facts, warm traversal at a flat 38, and a single snapshot-fact insertion or
withdrawal at no more than eight additional units. Wide-condition construction
is pinned separately so the entry charge cannot hide a large variable list.
Every required chain link is checked by withdrawing it from the certificate
context. `connected_condition_chain_expands_and_rechecks_at_multiple_sizes`
pins complete smart verification, expansion, and independent checking over
four chain sizes, including rejection when a link is missing.

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
For a function with complete checked execution evidence, call dependencies
come from its retained checked statements. A branch proved unreachable adds
no calls; a summarized statement, including a loop, conservatively adds every
call in its syntax. Missing dependency evidence falls back to scanning the
source body. Tactic dependencies and address-taken callback checks still apply.

Dependencies are collected once when an execution artifact is finalized.
Shared statement nodes are visited once across summary applications, using
identity keys rather than structural hashes. Certified claims share the
resulting immutable set; merging claims visits each distinct shared set once,
without copying a growing call set at every execution step. The
`checked_callee_summary_reuse_scales_with_input_not_product` and
`checked_callee_claim_reuse_shares_the_dependency_set` regressions grow both
dependency count and reuse count from 16 through 1,024 to guard this cost.

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

Select the function-proof driver before executing a wholly linear script.
The structural driver declines that shape without advancing its frontier;
the linear driver checks it once. Running a complete prefix merely to decline
and repeat it in another driver multiplies all statement and tactic work.
Regression coverage counts execution events at several proof sizes.

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
that locals, memory, and population observations are exact and that the bounded
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

Exact repeated-sample comparisons must measure the named operation itself.
`choose_projection_walk_is_deterministic_across_selected_body_sizes` measures
visits and persistent-node allocations inside the selected-body walk at 8,
32, 128, and 512 leaves. It checks one visit per selected conjunction node,
identical walk allocations between repetitions, and linear walk growth.
Proof setup and the checked choice's fact-index updates remain covered by
separate whole-operation work and indexed-allocation bounds. Those updates
must not enter an exact comparison of projection-walk allocations.

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
[`issues/README.md`](https://github.com/clicklang/click/blob/master/issues/README.md).

Atomic memory and resource source selection uses the kernel's candidate
indexes. Viewability and store goals read their block's viewability bucket;
read-defined goals first read the address's typed evidence, exact aliases and
equality spellings, plus that block's viewability facts. Memory separation
reads the unordered block-pair bucket and the non-memory residue, whose
resource containment can entail a memory separation. Candidates are still
checked by the kernel. Viewability pairs are selected by the kernel's
concatenation lookup rather than exhaustive pair trials. Candidate visits are
charged to `proposition candidate selection`.

Read-defined and resource goals retain a family fallback when no indexed
source succeeds: a computed address may need another read, and containment
may entail separation from a differently placed resource. Non-memory
separation queries also use this fallback. It visits the remaining family
once and tries individual sources; it never enumerates pairs. Viewability
and store source selection need no family fallback because their checker
consults only the goal block's viewability bucket. The existing cold
viewability shape index can still cost ambient work. Atomic trial contexts,
retained certificates and their checking use only selected dependencies.

`loadable_candidate_selection_ignores_facts_about_other_objects` and
`read_defined_and_separation_selection_try_indexed_sources_first` measure
candidate visits and complete derivation work beside 16, 32, 64 and 128
same-family facts. They check covering ranges, adjacent ranges, aliases,
contained separations and a gap that must remain unproved. Same-block negative
ranges exercise the wider bucket without exhaustive pair trials. Certificates
are checked independently and rejected when a required source is withdrawn.
`indexed_memory_sources_expand_and_recheck_at_multiple_sizes` checks one-source
and adjacent-source smart proofs, expansion and re-verification at four sizes.

Atomic certificate planning also maintains persistent syntax adjacency for
condition and proposition facts. Each key names a value variable or an
explicit pointer block. Symbolic blocks use their variable key rather than
a duplicate block entry. Formal arrays share the external address arena, so
that arena and the shared null block are omitted as keys: their offset
variables identify the objects. Scalar condition facts reuse their existing
variable adjacency; supplemental keys cover syntax the scalar index omits.
Scalar conditions with named values extend traversal through their explicit
blocks but are retrieved through their value variables. Snapshot equations
retain reverse block adjacency because a load may name their defining address.
Filing or withdrawing a fact adjusts only its keys; restrictions rebuild this
metadata from their selected facts. Typed pointer-read support is restored
through selected defining equations rather than scanning ambient definitions.
Construction is charged to `atomic dependency indexing`. Snapshot contents do not connect two
facts merely because they carry the same snapshot. Connection collection
includes pointer-offset variables, algebraic variables and function arguments
that a bitvector-only free-variable collector deliberately omits. A load also
looks up an explicitly stored value at its exact address, without synthesizing
loads from symbolic cell runs; nested load dependencies stop after 64 lookups
on one path. Those lookups are charged individually. Scoped
collection flags restore their previous values even during unwinding.

Each complete fact is shared across its variable and block buckets. Selection
deduplicates borrowed entries before copying retained syntax, so a wide
compound premise costs its syntax and adjacency entries once.
`wide_atomic_premise_cloning_scales_with_its_syntax` counts deep clone nodes
across construction, selection, certificate checking, and premise withdrawal
at 8, 16, 32, and 64 variables; doubling the input permits at most three times
the clone visits. This catches repeated tree copies that work-fee counters
alone cannot expose.

Candidate trials first check their named sources alone. When conditions are
needed, they walk only the condition buckets connected to the goal and source,
then rebuild and prove the restricted context. Separate condition and
proposition buckets prevent every single-source trial from visiting the other
proposition candidates. If no source succeeds, a joint selection follows both
kinds of adjacency. Condition goals first select their syntax component, including the value
stored at an explicitly addressed load cell and recent frame bounds. Registered
load variables follow the same exact-cell dependency as written loads, and their
live origin snapshots supply the frame history when canonical snapshots are
placeholders. Each registered load is expanded once per collection. If that query fails, its
selected conditions seed one joint fallback that includes frame and quantified
dependencies. Other atomic goals try narrow and widened selections. Retry
comparisons use premise sets, so reaching additional keys without adding facts
never repeats a kernel query. Widening is also skipped when it adds no seeds to the completed
component. A wider smart fallback admits ground and quantified facts and
follows variables in recent store addresses and call or loop havoc ranges,
at most 64 history edges per snapshot. Those buckets cost the facts they admit;
they are not a claim that the ambient context proves the goal. Every successful selection
still has to establish the goal in the restricted kernel context. Memo-identity
keys omit planning indexes and lazy query caches: retaining them for every transient restricted
context would keep otherwise dead adjacency versions alive. Fact-set equality,
hashing, and the memo-table limits remain unchanged. For smart
equality failures, the shared ambient oracle can reject a goal before another
history walk in a restricted context. Its positive answer never issues or
retains evidence: the selected restricted query must still succeed. The
former all-condition candidate trials and full-context retained leaves are
gone. Traversal is charged to `atomic dependency selection`; interruption returns no partial proof.

`atomic_memory_evidence_cites_only_connected_conditions` keeps one-source
evidence at one premise, equality-assisted evidence at two, and refuses a
range at an index not known equal. Beside 16, 32, 64 and 128 unrelated
conditions and memory propositions, retained premise sizes stay at 589 and
682 debug bytes and checking costs stay at 2 and 14 work units respectively.
`atomic_evidence_without_one_source_cites_connected_facts` covers the joint
quantified fallback: two premises, 872 debug bytes and 4 checking work units
at every size. It also extends one context by an unrelated condition and
memory fact before each query, over 8, 16, 32 and 64 additions, to pin total
construction and fallback work to near-linear growth across successive contexts.
Construction of the ambient input is outside the static query measurements.
Withdrawing each required premise invalidates the certificate.
`atomic_retained_evidence_expands_without_unrelated_conditions` covers
covering and adjacent ranges, a pointer alias, resource separation and the
quantified fallback through smart verification, expansion and independent
checking. `atomic_load_dependencies_ignore_other_snapshot_cells` checks that
an index loaded from one cell selects its equality, without retaining
conditions about other cells in the supplied snapshot. Cold canonicalization
may still charge the explicit snapshot input. Expanded proof bodies remain
the same size as unrelated requirements grow; whole-source work scales with
the input that must be parsed and checked.
