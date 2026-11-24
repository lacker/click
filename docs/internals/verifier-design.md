# Verifier design

This page divides the verifier into its parts and states what each part may
cost. Read it before proposing or reviewing a change to the verifier. A
proposal that adds work to the verifier names the part it changes and answers
the [design check](#design-check) below.

## Two parts: fast and slow

Every piece of the verifier is in one of two parts.

The **fast part** checks. It runs C one statement at a time, keeps the facts
of the current path, decides conditions, reads memory, tracks resources, and
applies simple tactics and certificates. Every proof pays its cost on every
step, and nothing can remove that cost later.

The **slow part** searches. It is the smart tactics, whose kinds in
`SmartTacticKind` are `Solve` (written `close()` and `close() using`),
`Arithmetic` (the arithmetic engine alone, whose written form
`arithmetic() using` the parser now refuses), and `Execute` (`step_until`, and
the stepping and splitting of the implicit tail that ends every proof script);
the implicit closer, `SmartSite::Implicit`; and the search helpers that fill an
argument a tactic leaves out. Its cost is optional:
`click expand` replaces a slow-part tactic with the fast-part steps it chose,
and the expanded proof runs no search.

That difference sets the rules. A slow-part search can be expensive, because
an author who finds it slow can expand it away. A fast-part cost can't be
removed, so it has to stay small.

## The parts

| Part | What it does | Part of | Main code |
| --- | --- | --- | --- |
| Frontends | Parse, validate, and lower C, C++, Rust, and Surface Click | fast | `src/languages/`, `src/surface/{parser,names}.rs`, `src/surface/validation/`, `src/surface/lowering/` |
| Symbolic execution | Run statements, calls, and loops on a symbolic state | fast | `src/kernel/eval*`, `src/kernel/functions.rs`, `src/kernel/loops.rs`, `src/kernel/proof/execution.rs` |
| Fact store | Hold the path's facts in persistent indexes, with the equality closure and the difference graph | fast | `PureFactStore` in `src/kernel/proof/facts.rs`, its `PureFactContext` component in `src/kernel/assumptions.rs`, `src/kernel/equality_graph*`, `src/kernel/difference_graph.rs` |
| Condition decision | Decide one condition (order, overflow, equality, consistency) from the facts | fast | `PureFactContext::decide`, `src/kernel/assumptions/condition_reasoning/` |
| Memory | Memory states, the memory derivation DAG, and load and store resolution | fast | `src/kernel/primitives/cell_store.rs`, `src/kernel/reasoning/memory_resolution.rs`, `src/kernel/memory_history.rs` |
| Resources | Ownership, views, borrows, folds, and separation | fast | `src/kernel/primitives/resource_algebra.rs`, `src/kernel/resource_tracker/`, `src/kernel/borrows.rs` |
| Simple tactics | Apply one checked step to a persistent proof state | fast | `src/kernel/proof/object.rs`, `src/surface/proof/proof_object/`, `src/surface/proof/checked_drivers/` |
| Proof construction | Construct ordinary proof steps and check local arithmetic primitives | fast | `src/kernel/proof/{object,fact_reasoning,arithmetic_special}.rs`, `src/surface/proof_certificate.rs` |
| Termination | Plan recursion heights over the call graph, then check them | fast | `src/kernel/termination.rs` |
| Smart tactics | `close()`, `step_until`, the implicit tail and its closer | slow | `src/surface/checking/{arithmetic_engine,simplex}.rs`, `src/surface/proof/{smart_closures,smart_execution,selected_arithmetic}.rs` |
| Search helpers | Fill an elided premise, fact, resource instance, or guard | slow | `src/kernel/search/proposition_search.rs`, `src/surface/proof/fixed_state_proofs/` |
| Expansion and printing | Write a slow-part result as fast-part tactics, and print source | tools | `src/surface/expansion.rs`, `src/surface/printing.rs` |
| Tools and budgets | `profile`, `audit`, traces, work accounting, and budgets | tools | `src/bin/`, `src/instrumentation.rs` |

The kernel checks everything the fast part concludes, so a bug in the slow
part can lose a proof but can't prove something false. The tools decide
nothing.

## The fast-part rule

A fast-part operation does indexed lookups and work proportional to its
explicit input and the state it produces. It doesn't scan.

- **Input** is what the operation names: a tactic's written arguments, the C
  statement being executed, the condition being decided, and the definitions
  those name.
- **Output** is the state it adds: new facts, new paths, unfolded members, a
  certificate.
- **A lookup** reads an index by a key built from the input, such as the
  facts that mention a variable or the cells of one block.
- **A scan** reads a collection that grows with the program, the path, the
  facts, the states, or the resources, and then keeps only the entries it
  needs. This rule has no exceptions: a fast-part operation doesn't scan even
  the facts "related" to its input unless an index hands them over by key.
  Visiting each indexed entry once is not sufficient: a bucket, equality
  class or chain can grow while the explicit operation stays fixed. A traversal
  needs an explicit-input/state-delta bound, or an amortized argument across
  the whole proof including cold queries and persistent branches. Discovery
  without that bound belongs in expandable search.

Writing `N` for the size of the selected C, Click, and proof text, `q` for the
operation's input, and `d` for its output, one operation costs
`O((q + d) polylog N)`, and a project written entirely in simple tactics
verifies in `O((N + D) polylog N)`, where `D` is semantic output such as
enumerated paths. [Verification efficiency](verification-efficiency.md#complexity-contract)
gives the full contract.

The condition decision is in the fast part. Simple tactics such as `fold` and
`step` call it to check a premise, and expansion can't remove it, so it
follows the same rule. Its per-query fuel is a safety net that stops a
runaway decision, not a license to scan.

The fact collections of a `PureFactContext` (`condition_facts`,
`order_condition_facts`, `prop_facts`) charge one unit of deterministic work
for each element a full iteration visits (`src/kernel/fact_collections.rs`),
so a scan shows up in scaling tests and tactic budgets wherever it is written.

Remaining checking candidates and gaps in scaling evidence are organized by
operation in the [operation audit ledger](verification-efficiency.md#operation-audit-ledger).
That inventory distinguishes source candidates, scoped regression evidence and
unaudited routes; it is not a claim that the whole verifier already meets the
contract.

## Enforced search access

`SearchPermission` is an opaque capability constructed only inside
`surface::planning`. Ambient `scan_for_search` and the planner's atomic,
condition, proposition and disjunction views require it. Checking can use
indexed queries and explicit inputs without that capability. The smart
closer's disjunction adapter keeps capability construction inside planning.
The dedicated diagnostic API returns a bounded sample (at most 32 facts)
and a total count; it exposes no ambient iterator. Viewability witness enumeration
requires planner permission and charges every visited fact. Viewability
diagnostics use the block-keyed candidate index.

Every Cargo build runs `build_support/search_boundary.rs`. It follows Rust
module declarations, skips test-only modules, and rejects kernel dependencies
on Surface code. It also pins the functions and reference counts allowed to
use the diagnostic sampler. `SelectedFacts` separates atomic reasoning from the
ambient fact store: checking constructs it from an explicit proposition list;
planning may reuse a persistent context through `for_search`, which requires
`SearchPermission`. The type has no mutable dereference or unchecked context
constructor. Retained certificate leaves construct it from their named premises.
Normalization lives in `surface/checking/normalization.rs`.
Branches retain their parent fact context and extend a cheap persistent clone.
An opposite exact condition assumption records `false`; it never replaces the
original condition or deletes its index entries. On a context holding this exact false
premise, scalar specification addition, subtraction, multiplication, division and
remainder construct their terms without ambient facts: falsehood discharges their
arithmetic guards. Consistent contexts retain their usual definedness guards and
provenance, and executed C keeps its undefined-behavior checks.
Fact contexts only grow and fork; there is no fact withdrawal. A branch
retains its parent context and extends a persistent clone, and a negative
control queries the context built without the premise.
`tests/search_boundary.rs` checks rejected dependencies, aliases, method
references, macro tokens, extra diagnostic scans, and capability privacy.

`ResourceContext::admit_without_discovery` admits an explicit resource batch
through indexed ownership checks and exact exclusive-resource checks. It returns
a successor, a conflict, or an explicit missing separation proposition, with
no successor on a miss. `try_compose_checked_ownership_and_occurrences` preserves
that result while retaining the inserted occurrence IDs. There is no automatic
ownership-discovery fallback. The fast operation has a required test-build
discovery guard.

The symbolic boundary checker uses producer-published memory indexes: constant
intervals plus at most one selected symbolic owner, with direct endpoint bounds
and equality-class coverage. It never enumerates an owner bucket or alias class.
A maintained projection of the actual raw-memory frame caches its Surface-
representable footprint. An unsupported boundary asks for `separate` between the
new range and that footprint. Admitting an explicit separation proposition
indexes its written memory leaves; a query selects that retained premise by
range and canonical frame identity. Adding a different range invalidates the old frame
match. Footprint preparation belongs to ownership deltas, and explicit-premise
indexing pays for the written proposition.

Checked call returns retain entry-borrow origin beside each emitted resource
occurrence, including after guarded clauses are skipped or dependent clauses
are deferred. Restore these borrows before admitting the other outputs. Produced
composite frontiers are checked against the restored frame plus the existing
escrow, so a produced body cannot duplicate a returned borrow. Borrowed composite
bodies retain their existing check against the original frame because their
bodies may read post-call memory. Occurrence results
retain emitted order even though restoration happens first. Raw return-description
validation does not authorize restoration from a role marker.
An entry-borrow marker is recorded only when evaluation retrieves the checked
entry occurrence; an unmatched or deferred description keeps ordinary admission.

Return construction captures each source occurrence ID from admission alongside
its entry-borrow origin. Composition pairs that ID with the destination ID
returned by restoration or admission. Core projection selects the owned source
by its occurrence ID and attaches observations to the paired destination; it does
not enumerate equal descriptions or reconstruct occurrence ranks. Equal resource
descriptions retain independent support and removal lifetimes across the return.

Direct order queries read persistent constant-bound extrema and strict-upper
witnesses keyed by the written or canonical endpoint. Admission updates only the
new fact's endpoints; queries do not filter an endpoint's condition bucket.
The build boundary rejects condition-side enumeration in order/overflow helpers.
General interval reconstruction and anchored equality still have separate audit
targets in the roadmap.

Prepared memory-access checking receives `SelectedMemoryAccess`: one indexed
supplier and its retained graph checkpoint, with no candidate iterator. Read,
write, storage, pointer-position and kept-frame checks validate that supplier's
quantity, provenance and coverage; a refusal does not try another supplier.
Whole-scalar consumption also requires uniqueness, established by inspecting at
most two indexed entries. Explicit footprint composition retains its separate
output-sensitive interface. The resource checker cannot import or call the raw
access-candidate API. Object-provenance queries use the object-identity index's
nonempty witness or singleton symbolic supplier. Provenance/opaque-bounds
fallback comparisons use a singleton direct alias after indexed equality fails.
Framed pointer-value recovery requires one address alias and one full-pointer
source in that address bucket; multiple states do not authorize a hidden
source search. Complete-read, state, provenance and bounds checks still
apply to the selected source. The direct order, supplier, and provenance-source
lookup stages have their own `CheckingWorkScope`, charged to one explicit query
key. These scopes do not excuse scans or cover general memory-history traversal.

Selected-context construction starts from an empty fact store, retaining only
reasoning policy, variable allocation bounds and typing metadata queried by the
selected load variables. It never clears the inherited graph's pointer sources.
Step-refusal pure-fact listings use the capped sampler and identify truncation;
conversion-condition refusals use indexed atomic checks and structural
reflexive guards (including under native int32 universal binders), never general
proof search. At a `have` scope opening or an unfold, an unmet mandatory
condition is exposed to the ordinary obligation probe. The implicit solver
proves it at the operation's input state and retains its explicit `have`
certificate before the operation; expanded proofs check without implicit
solving. The fast checker itself still refuses an unmet condition. Probing a
`have` stops at scope opening, so requirements from its body cannot escape
nested binders. Pure theorem conclusions retain their mandatory requirements
until entry proof checking. Explicit leading `have` steps can establish them;
otherwise the implicit solver retains an equivalent `have` prelude. The
remaining script starts only after these requirements are established, and
expansion checks the prelude with implicit search disabled. Native universal
introduction supplies the fresh binder's intrinsic machine bounds as facts;
these bounds are not inserted as implications into the lowered proposition.
The build boundary checks these diagnostic entry points.

Viewability checking looks up an exactly stated view directly. A candidate
address-shape bucket supplies implicit evidence only when it contains one fact;
an ambiguous bucket is refused without iteration. The planner's
`search_memory_loadable_candidates_for_base` requires `SearchPermission` and
charges each visited candidate. Search can choose a covering view and expansion
writes `transport(source, target) using { ... }`; explicit selection checks in
a restricted context. The build boundary rejects kernel calls to that search
entry point and rejects the test-only whole-block census. The atomic coverage
fallback uses the same checked candidate lookup. Checked view lookup uses
structural offsets, the maintained affine class coordinate and its unique
concrete storage anchor; it never enumerates the alias class. A singleton
selected source may have another block form: checking aligns the two
supplied addresses through the graph and retains bounds, lifetime and
structural-distinctness checks. Preserve existing same-block endpoint expressions
unless the addresses are already equal; coordinate projection must not obscure
their stated bounds. Other forms require search permission.
The build boundary rejects alias enumeration in these migrated view queries.

Condition-fact queries use the maintained truth index and singleton canonical
shape/variable buckets. Atomic memory-order queries use indexed truth for both
orientations, retaining the comparison carrier; compound memory queries still
require their canonical key or an explicit form. No query enumerates scalar
classes to select a premise. Other condition-side bucket helpers remain audit
targets.

Read-validity evidence uses exact typed/state membership and singleton
address buckets under structural, affine and concrete storage keys. A selected
source retains type, address, no-write and lifetime checks. Alternate-source
enumeration requires planner permission. Kept-frame lookup uses the prepared
address index; its raw fallback accepts singleton structural/coordinate buckets
or a unique directly stated alias, never the rest of the block. Opaque reads
do not trigger history resolution just to discover a supplier. The build boundary
pins these query paths; remaining resource-index audits are in the roadmap.

`instrumentation::CheckingWorkScope` gives a checked operation its own allowance
inside or outside a tactic. Atomic memory-condition matching measures one
comparison of two scalar atoms; its allowance is independent of enclosing
search. Compound terms and offsets need a separate explicit-size measure before
receiving the same coverage. Selected-context construction installs it with the
number of selected entries; ambient fact count cannot enlarge the allowance.
A scope exhaustion names the checked operation and enclosing tactic/source site
and reports an engine performance defect. Every unit still charges the enclosing
tactic and whole-run budgets once, so many cheap checked alternatives can exhaust
search without a checker defect. Nested scope allowances do not add duplicate
units to profiling. This is initially installed on selected-context construction;
it does not yet classify every checker reached by a smart tactic. Further sites
must name their explicit input/output measure and retain scaling regressions.

This is an incremental boundary, not a proof of complexity or a complete Rust
dependency resolver. Upkeep APIs and ordinary collections still need auditing.
Do not evade the boundary by relabelling a scan as upkeep, adding a re-export,
or widening an allowance. Review any boundary change with the same design
check as the reasoning it permits. Scaling tests remain necessary for indexed
buckets and repeated work.

## The slow-part rule

A slow-part search may scan, try alternatives, and recurse, under three
conditions:

1. **It is bounded.** It runs under a deterministic work budget and fails
   promptly, with a bounded diagnostic, when the budget runs out.
2. **It is expandable.** `click expand` writes what it found as fast-part
   tactics, or as the same tactic with its elided argument written out.
   After expansion no search runs.
3. **It is checked.** It advances the proof only through fast-part
   operations, so the kernel checks everything it concludes.

Writing a search out requires every fact it cites or proves to raise to a
Surface AST that lowers back to it; the
[raise-lower principle](raise-lower-principle.md) states that rule. A search that
can't be written out as explicit tactics isn't allowed in the
slow part either: then there's no way to remove its cost, which makes it fast
part, and fast part may not search. [Smart and simple
tactics](../concepts/smart-and-simple-tactics.md) defines the tactic classes
including `close()`, `step_until`, the implicit tail and closer, and searches
that fill elided arguments.

## Design check

Answer these before proposing a verifier change that adds work.

1. **Which part does it change?** Name it from the table above.
2. **Fast or slow?** If it adds reasoning to a fast part, ask first whether
   it could be a slow-part search instead: a new strategy in `close()` or
   the implicit closer, or a helper for an argument a tactic already takes. Put it there
   unless every proof needs it on every step.
3. **If fast:** which index serves each read, and what is the key? Which
   scaling test grows both unrelated and related input (more facts about
   other values, and a longer chain of facts about this one) and shows the
   work stays near-linear? "It's cheap" and "the corpus didn't get slower"
   don't answer this.
4. **If slow:** what does `click expand` write in its place, and what
   explicit syntax lets an author write that result without the search? If
   that syntax doesn't exist, adding it is part of the change.
5. **Is lowering still fact-stable?** A change to lowering or evaluation may
   let facts refuse a term, discharge its obligations, or add side facts, but
   never change the term it produces; equalities belong to the equality
   graph ([fact-stable lowering](raise-lower-principle.md#lowering-is-fact-stable)).
   Run `scripts/audit.sh fact-stability` before and after, add no new
   `differs` lines, and report any change in its `refused` and `paths:N`
   counts.
6. **What does it fail with?** A slow-part miss names what wasn't found and
   how to supply it. A fast-part refusal names the rule it checked.

A change that can't answer question 3, 4, or 5 doesn't go in.

## Vocabulary

Proposals often name a mechanism rather than a part. These are the parts the
common mechanism names belong to.

| Term | What it is | Part |
| --- | --- | --- |
| condition decision, `decide` | Decides one condition from the facts | Condition decision (fast) |
| difference graph | Index of `x - y <= c` bounds between values | Fact store (fast) |
| equality graph, equality closure | Index of which terms are known equal | Fact store (fast) |
| order walk, order path | Removed: order inside a decision is read from the difference graph | Condition decision (fast) |
| overflow intervals, bounds | Value ranges read to decide overflow | Condition decision (fast) |
| memory resolution | Finds the value a load reads across stores | Memory (fast) |
| memory derivation DAG, state, cell store | How memory states and their cells are stored and related | Memory (fast) |
| DAG bridging | Relating a load at one state to cells of an earlier one | Memory (fast) |
| carriers, compositions, separation | How owned resources and their disjointness are represented | Resources (fast) |
| fold, unfold, views, borrows | Building, opening, and borrowing resources | Resources (fast) |
| proof object, proof step | The persistent proof state and one checked change to it | Simple tactics (fast) |
| certificate | An explicit derivation the kernel checks without search | Certificates (fast) |
| planner (signed, `Integer` affine, special, simplex refutation) | Chooses an ordinary arithmetic proof plan | Smart tactics (slow) |
| selected-premise arithmetic | the solver's choice of the facts and type ranges arithmetic refutes an arithmetic goal from | Smart tactics (slow) |
| rewrite search, equality chain | the solver's search for rewrites that close a goal | Smart tactics (slow) |
| premise selection, connected premises | Choosing which facts a tactic uses | Search helpers (slow) |
| transport planner | Choosing the facts a bare `transport` carries | Search helpers (slow) |
| theorem premise cascade | Finding the premises of a bare `apply` | Search helpers (slow) |

## Where the details are

- [Verification efficiency](verification-efficiency.md): the complexity
  contract, representation requirements, regression policy, and notes on
  how specific operations meet the contract.
- [Smart and simple tactics](../concepts/smart-and-simple-tactics.md): the
  tactic classes.
- [Testing](testing.md): how to write a scaling test and measure deterministic
  work.
- [Architecture](architecture.md) and [Kernel](kernel.md): the code layout.

### Direct intervals and equality evidence

Fast signed-interval checking reads maintained endpoint extrema and scalar-class
summaries, then recurses only over the written expression. It does not walk a
symbolic order component: derive and state an intermediate bound explicitly
when a goal needs a chain. Contiguous written disequalities are maintained as
excluded-value runs, so trimming interval endpoints takes indexed lookups.

Constant-equality evidence selects numeric extrema and at most one unambiguous
symbolic source per direction. Anchored memory equality checks exact membership
or one singleton source per written endpoint, with the same memory-resolution
and state checks. Ambiguity declines; it does not enumerate the endpoint
bucket. For a transported read's constant value, prove the current read equals
the saved read first, then normalize using that equality and the saved value.
This explicitly supplies the connection that an ambiguous constant endpoint
bucket cannot choose. Build-time boundary checks reject the removed enumeration routes, and
`condition_buckets` scaling regressions grow both related and unrelated state.
Other remaining checking walks are tracked in the [operation audit ledger](verification-efficiency.md#operation-audit-ledger).

### Written literal and ownership queries

`direct_scalar_constant` accepts a literal or an exact stated Int32/UInt32
literal equality in either orientation. The existing scalar-class summary
nominates its value; ambiguous summaries decline. A chain or arithmetic folding
alone does not supply the written premise: derive and state the endpoint
literal equality explicitly. Checking reads at most four exact premise keys,
without traversing equality evidence edges.

Store ownership footprint lookup uses only the additive bases written in the
access. It does not enumerate their pointer alias classes. When a resource is
owned under another form, state the alias and separation explicitly and
use `transport ... using` to carry the required read across the write, as in
`mdtests/do_while_restored_field_frame_remains_separate.md`. Build-boundary
checks reject the removed evidence and alias enumeration routes. Automatic
store preservation selects at most one owned member per written base from the
persistent base index; a crowded bucket declines without visiting its members.
The parameter partition uses the same singleton rule for cached reads. Without
current store owners, historical selection reads the root and at most one
composition per written base; it does not enumerate crowded historical buckets.
A miss may forget the cached value. State separation and use explicit transport
when that value is needed, as in
`mdtests/crowded_store_ownership_uses_explicit_transport.md`. Deterministic
regressions grow both member and historical-composition buckets through cold,
repeated and unsuccessful store queries with a fixed cache. Boundary checks
reject the former enumeration helpers in these store paths.

Cached-value preservation does not retry the general
`owned_composition_store_separated_evidence` search after the store's earlier
checks miss. The build boundary forbids that call from
`without_possible_aliasing_cells`; explicit transport and memory-history
checking retain their separate support. The store also does not call
`pointers_proven_disjoint_by_explicit_range_for_memory_resolution` directly.
The direct-range fallback is also absent for both scalar cells and union
views: an unresolved cached value is forgotten. The build boundary rejects
restoring either range helper directly. Scalar-cell and union-view preservation
also use `pointers_directly_distinct_for_store`, not general memory-resolution
distinctness: structural byte shifts, exact pointer/index inequalities and
exact signed-order facts supply direct evidence. The index facts are read by
key from the pair `common_base_store_indices` returns, a structural reading
of the two offsets: two `int32` indices are compared as their Integer values
(`index_comparison`), and two 64-bit scaled indices of one width and
signedness, or one beside a constant offset of whole elements, as the native
`uint64` or `int64` comparison a stated `((n - 1) as uint64) != 0` lowers to,
read in both orientations. A mixed 32/64-bit or mixed-signedness pair has no
key. Regression:
`wide_store_index_lookup_ignores_unrelated_facts_and_same_array_cells`. Private-local separation reads
the addressability registry and an indexed equality-graph block coordinate;
it does not enumerate aliases. A miss forgets the cached value. The boundary
rejects general resolution, range search, alias enumeration and order-path walks
in this helper. Growing same-block separation buckets leave cold and repeated
miss work unchanged, while written index disequality still respects access
widths.

The implicit tail supplies that direct evidence in the slow part, not the
store. After a smart statement step (`try_statement_step_with_retries`),
`retry_statement_keeping_store_cells` diffs the statement's input and output
cell maps (`kernel::search::store_separation`, proportional to the changed
cells, at most 64 pairs compared), pairs each dropped cell with a written cell
of the same array, and states the index disequality the store-time check
reads, by construction from the two index words
(`synthesize_store_index_disequality`: `((m - 1) as int32) != 0`,
`((n - 1u64) as uint64) != 0u64`). It proves at most four at the pre-state with the narrow closure
`try_index_disequality_closure` (signed interval certificate, order
refutation, disequality bridge), retains them as
`have`s and reruns the statement; expansion writes those `have`s and the
expanded proof searches nothing. A disequality it does not prove is kept,
already raised, in the path's presentation (`store_separation_misses`, at
most 32, carried across joins as arm suffixes) and is never read while
checking. A refusal whose goal reads a cell a recorded miss dropped explains
that read with one bounded history walk and, when the walk stops at that
miss's store, prints the statement and the raised fact; it does not search
to raise anything. The solver's last strategy,
`try_disequality_by_refuted_equality`, proves a disequality from a connected
one by cases on the goal's equality, so the Integer fact `m - 1 != 0` gives
the word fact where the word cannot wrap. Regressions:
`store_index_separation_search_scales_with_unrelated_stores_and_facts` and
its `size_t` sibling
`wide_store_index_separation_search_scales_with_unrelated_stores_and_facts`.
After it, `try_element_address_disequality` reduces a goal
`&q[j] != &q[0]` whose two addresses share a base and scaled indices of one
width and format to `have j != 0` (written the same way, proved by a nested
`close()`) and closes it with
`apply(click::separation::distinct_elements(q, j, 0))`, the explicit law
expansion writes.

Automatic store byte-gap eligibility reads an exact stated endpoint order;
it does not follow recorded order chains or invoke general condition decision.
For an order that follows transitively, write the endpoint bound before the
store (for example `have i < j by close() using { i < middle; middle < j; };`).
That search expands into explicit proof steps. The checking boundary rejects
order-walk helpers in `one_element_gap_separates_bytes`; deterministic tests
hold the store fixed while increasing both successful and missing order chains.

Store preservation of compact runs uses constant byte geometry or the cached
signed interval of the written index. It forgets the entire possible write
window as an interval, including for runs whose values are symbolic loads or
copies. The existing bounded ownership selector also handles a run as one
complete byte footprint. One explicitly stated separation selected by the
run/write address anchors can likewise retain the whole run, provided both
complete byte footprints fit.
The lookup inspects at most two candidates and declines an ambiguous bucket.
An otherwise unplaced write forgets the whole run. It does not enumerate
logical slots or search separation-fact buckets. Fixed-offset writes query hole
coverage only for the two partially covered boundary intervals, including when
value widths exceed slot strides. Initialization records and immutable
source history remain available; explicit separation and `transport` recover
selected values, as in
`mdtests/store_geometry_uses_explicit_order_and_transport.md`. Scaling tests
grow order chains, separation buckets and logical run lengths independently;
the build boundary rejects the removed search and per-slot routes.

Named `unfold` publishes the constructed successor composition so explicit
separation can use the existing checked-borrow partition rule. This publication
follows body evaluation; temporary body assumptions must not index the caller
frame. Incoming borrows remain distinct from ordinary read observations, and a
caller cannot lend the owner it transfers. The named-unfold alias-call and
two-view refusal fixtures pin these restrictions.

Non-memory owned-support selection nominates one indexed witness. Exact facts
and exact owner-backed projections use their fact keys; non-exact queries
require a singleton resource, prepared address-class/shape, or shape bucket.
A selected candidate must entail the requested quantity and resource; failure
never searches another candidate. The projection index is persistent and updated
only for inserted or removed non-memory projections. Its support occurrence
still names a live owner, so equal unbound views cannot erase that association.
An owned observation without selected live support is refused; zero-quantity
observations still establish no body authority. Scaling tests cover exact hits,
misses, crowded quantity buckets, duplicate unbound views, and parent/child
isolation after owner removal. The build boundary forbids candidate search in
`direct_nonmemory_support_entry`.

Memory owned-support lookup nominates one whole-range supplier through exact
footprint, exact-start singleton, covering-interval, or singleton-base indexes.
It checks that occurrence's
quantity, alignment, and containment once; a failed check does not request a
second candidate. A selected projection must still name a live owned support
occurrence. This route never enumerates fragment starts, follows a fragment
chain, or scans incident order premises. Explicit fragment composition retains
its separate iterator. Build boundaries pin both the support caller and
`MemoryFactEntries::single_supplier`; scaling tests cover exact hits, symbolic
misses, and a fixed-span refusal beside increasing short owned fragments.

One-fact memory evidence selection (`directly_supporting_fact`) uses the same
indexed nomination for owned and viewed requirements. It aligns and checks the
selected supplier once, requires positive quantity from an owner, and returns
that exact held representation. A refusal does not try other candidates.
Its dedicated memory helper is covered by
the candidate-search build boundary. Repeated fixed-span misses beside growing
short fragments and exact early/late hits have separate scaling coverage;
selecting one fact does not compose a partition or normalize suppliers.

Memory-view satisfaction uses that same indexed one-fact check. Empty views
and exact held views retain their direct checks; other views require a selected
supplier covering the whole query. Failed selection does not enumerate the
resource-key bucket or normalize a collection of adjacent fragments. Scaling
controls grow both owned and viewed fragments beside a fixed missing view,
with repeated queries and exact early/late hits. Non-memory view queries and
memory queries for other ownership quantities retain separate routes.

Incremental memory-view consumption uses the same single-supplier check.
Observing a view returns the original context, preserving supplier occurrences,
borrow bindings and split origins. It does not consume an owner or construct a
normalized resource context. A view spanning adjacent fragments needs explicit
composition before this check; a failed lookup does not search for a partition.
Scaling controls cover cold and repeated misses and exact early/late hits for
both owned and viewed suppliers, and identity tests pin unchanged storage.

Call planning retains memory split origins while constructing residual owners.
Each new residual occurrence maps directly to its original pre-reservation
owner in a call-local persistent map. Repeated splits propagate that original
identity, never a predecessor link. Failed speculative reservations discard
their map updates with the candidate state. The selected live residual must
have the expected origin; equal-looking owners do not substitute for it.
This replaces alternative-owner enumeration and the subsequent coverage
reconstruction. Joins that create fresh owners do not infer a single source
identity. The map changes only with the selected split output and is discarded
after planning; ordinary resource contexts acquire no history or new facts.
Boundary checks forbid the removed search and context-history reconstruction;
scaling controls grow incident bounds, observations, and successive splits.
Borrow bindings retain persistent indexes of bound occurrences, keyed by exact
view and by written memory base or nonmemory resource shape. Updates touch
only the changed occurrences. Exact requests nominate the first indexed bound
identity; nonexact requests nominate through a singleton bucket or binding
map. If metadata nominates none, the live-resource index may nominate one
view, whose binding is read directly. This handles retained loop metadata
beside a fresh live occurrence without scanning either set. Selection checks the actual live view, then the ledger
checks the binding and participant and the planner checks its permitted
coverage. An unsuitable nominee does not cause a retry. The empty binding map
requires no observation discovery. These are metadata indexes, not e-graph
facts or new resource authority. Branches share persistent roots, and removal
or replacement updates only that branch.

Call planning uses this selection for parent and callee bindings; boundary
guards forbid observation enumeration and implicit fragment coalescing in
`borrows.rs`. Refusal classification may consult one indexed
observation witness; that lookup grants no borrow authority and never retries. When lending a selected owner, consumption receives that occurrence
directly, aligns the requested slice and consumes only it, retaining split
origins with the successor. It does not rediscover a supplier or join other
fragments on failure. Scaling controls measure both selection and complete
calls beside increasing unbound observations, plus exact lookup and branch
isolation beside increasing bound occurrences.

Loop-body construction carries bindings at the producers of declared, framed,
and owner-derived views. Each producer retains the inserted occurrence and
attaches the bounded source selection before normalization; bound views retain
their identities. The final binding overlay visits only the produced bindings,
sharing the inherited persistent map. It never searches the completed body or
entry context. With an explicit view interface, retained-frame construction
selects the state's declared scalar blocks and queries owned occurrences
by block. `MemoryBlocks` maintains that persistent subset on declaration,
replacement, removal, and branch joins; the index is excluded from semantic
memory identity. No heap-owner or observation enumeration is involved. The
complete-constructor regression grows both withheld heap ownership and heap
block declarations, checks fixed output, and measures repeated work and
persistent-map operations. The route without an explicit view interface still
retains the withheld frame's views, with work charged to that output.

Call preparation classifies implicit local storage with
`has_no_explicit_memory_for_local_storage`: a block-index absence check and a
retained count of memory facts with nonconcrete allocation identities. Explicit
memory anywhere in that block, nonconcrete memory identities, and pointer-alias
facts alongside memory resources select the explicit route. It does not search
for complete fragment coverage or enumerate views to establish absence. This
is conservative refusal, not new alias or ownership evidence. The complete-call
control also bounds completion beside unrelated constant owners.

The constant-range neighbour index stores exact signed `i128` byte coordinates:
this covers signed narrow bounds and every unsigned native endpoint multiplied
by its `u32` element width. Large same-base native coordinates use the same
predecessor/successor validity checks as small ones, without a block scan or
machine-integer narrowing. Known-empty intervals count as represented but do
not enter neighbour ordering, where they could hide a containing owner.
The pair overlap predicate and incremental insertion agree that a constant
empty interval has no overlap obligation. Index removal uses the same rule
and preserves branch isolation. Scaling controls
hold an insertion fixed beside growing owners above the old signed limit;
semantic controls retain overlap rejection, mixed widths, maximal endpoints,
empty/reversed intervals and persistent removal.

The same index strips a literal leading or trailing byte displacement from a
range's base and adds it to the exact coordinates. Pointer construction already
combines trailing constant displacements, so this inspects one offset node;
it does not normalize a symbolic expression, traverse history, or consult
facts. Original resource terms and occurrences remain unchanged. Constant
translations of one symbolic base share neighbour checks and the full-context
sweep; the overlap predicate uses that same geometry, including native bounds
and mixed element widths. Refusal and removal controls retain distinct symbolic
origins, negative displacements, empty ranges, aliases and branch isolation.
An unrelated origin in the same block does not disable this check: the existing
root membership count is compared with the selected origin's coordinate count.
When those counts match, the queried root contributes only its adjacent keys
and first/last duplicate occurrences (at most four nominees). Root discovery
still includes aliases, and roots reached through facts keep their checks.
Symbolic bounds or multiple coordinate origins within the queried root fail
the coverage guard and retain the existing route. No root members are scanned
to establish coverage, and no new index or fact is created. Scaling controls
grow the queried root beside an unrelated owner; semantic controls retain
alias collisions, duplicate insertions, unindexed members and branch isolation.

Call completion inserts returned outputs and recovered escrows into the valid
persistent frame using incremental conflict checks. It never normalizes a whole
memory block or revalidates old-old ownership pairs. Returned-view authority is
checked for the declared output delta recorded during contract evaluation;
unchanged caller views and supported projections retain their existing authority.
Escrow presence uses exact representation lookup rather than a supplier search.
`returning_one_borrowed_owner_does_not_rebuild_its_memory_block` measures entry,
recovery, and the complete call beside increasing disjoint same-block fragments,
including repeated queries and persistent-map work. Build guards prohibit the
removed frame iteration and normalization APIs in these completion paths.
Nonconstant insertion candidates remain a separate audit target.

Explicit ownership composition for a narrow- or native-indexed range
with unit quantity uses `consume_unit_owned_memory`. It nominates one whole
supplier, or consumes successive indexed fragments through the existing reservation
operation, stopping at the first gap or unsuitable supplier. It retains split
origins when requested and edits a persistent branch; it neither collects a
candidate frontier nor retries alternatives. Selected native-indexed suppliers
keep their original 64-bit bounds, element width, and carrier; their consumed
pieces must have exact aligned coordinates and checked lengths. The constant
neighbor index orders narrow and native ranges by checked byte coordinates,
so unfolding does not scan unrelated same-base suppliers whose constant byte
coordinates fit that index. Native request lengths use checked unsigned
subtraction and multiplication, then exact conversion to the indexed byte
cursor; native pieces are never narrowed to 32 bits. An unrepresentable length
or coordinate refuses composition without entering the candidate fallback.
For a native request, each selected supplier must satisfy its typed access
provenance, as the previous whole-range entailment route required.
A constant native request may have symbolic intermediate partition points.
When its nominated supplier has symbolic bounds, consumption follows unique
exact-start entries, applying the existing binary range-composition rule.
Every selected piece must lie inside the request; a gap, ambiguous successor,
cycle, wrong provenance, or non-unit owner refuses without trying alternatives.
Consumption and non-consuming queries share this persistent operation. Scaling
controls grow unrelated same-base fragments beside a fixed symbolic partition.
Symbolic unit-owned requests use the same singleton supplier and exact-endpoint
composition, without enumerating incident order bounds or candidate frontiers.
A selected narrow cell written `(p + i)[0..1]` is restated as `p[i..i+1]`
before containment and adjacency, retaining its carrier. This uses the existing
exact coordinate rule on that piece, not an alias or supplier search.
Complete-fold controls keep the footprint fixed while growing incident order
facts, including refusal and successful composition; selected-piece controls
measure larger actual partitions separately. Other quantities remain an audit
target. A build guard forbids candidate enumeration in this consumption path.

Non-consuming `satisfies_fact` queries for all unit-owned memory ranges use
that same indexed consumption operation on a persistent copy.
Success establishes the requested ownership without changing the caller's
occurrences; failure stops at a gap or unsuitable supplier. They never enter
the enumeration/normalization fallback. Scaling controls hold the requested
range fixed beside growing rejected fragments for both narrow and native
constant bounds, then separately grow the selected contiguous pieces; both
include repeated queries and persistent-map
work. Symbolic-query controls also grow incident order facts, including cold
and repeated refusals, adjacent composition and saved-cell coordinates; queries
preserve parent ownership and branch isolation. A structurally known shorter
selected footprint skips whole-supplier coverage before adjacent composition;
byte lengths include element widths, with no order-premise or pointer-offset
search to establish that refusal. Typed queries check each selected piece's
access provenance for both narrow and native coordinates; narrow byte
transfers retain their suppliers' carriers instead. After the first
piece, constant fragment composition requires exact adjacency and refuses
selected overlapping suppliers. Other-quantity memory satisfaction routes
remain separate audit targets.

A proof can combine differently sized owned fields by folding a resource whose
body owns the complete object, then unfolding it before a call that borrows the
whole object. This is an explicit ownership construction, not a new separation
axiom or pure fact. The complete fold/unfold scaling control measures successful
mixed-width composition and a fixed early gap beside growing rejected fragments,
including repeated work and persistent-map visits. A native-request fold control
also measures a whole owner, two-piece composition, and a fixed early gap.
Borrow planning itself does not perform that composition automatically.

Declared-resource lowering selects parameter values from the names in its
explicit arguments, including quantities and nested resource-type arguments.
Outcome-proposition lowering against an indexed assumption context likewise
selects only the names its proposition mentions. Both use `ParameterIndex`
and construct array references from the selected values. Neither selection
uses facts to change the term being lowered. The observation regression
`observing_one_owner_ignores_unused_parameters` holds one owner and three
observations fixed at 4/16/64 function parameters; first and repeated work must
remain flat as unused parameters grow.

An explicit loop read frame can select a flat range withheld from the loop
body by the checked ownership partition. The loop history retains that
persistent frame even when a conditional collection's conservative mutable
footprint overlaps it. Selection reuses the indexed kept-range query with no
composite expansion; a singleton covering range must include the entire read.
A scalar cached prefix does not preserve a complete pointer. Distinct retained
frames have distinct havoc identities, and a later overlapping store still
invalidates the read. This adds no implicit store-preservation search.
