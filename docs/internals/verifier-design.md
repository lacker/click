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
`SmartTacticKind` are `Solve` (written `solve()` and `solve() using`),
`Arithmetic` (the arithmetic engine alone, whose written spelling
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
| Fact store | Hold the path's facts in persistent indexes, with the equality closure and the difference graph | fast | `PureFactContext` in `src/kernel/assumptions.rs`, `src/kernel/equality_graph*`, `src/kernel/difference_graph.rs` |
| Condition decision | Decide one condition (order, overflow, equality, consistency) from the facts | fast | `PureFactContext::decide`, `src/kernel/assumptions/condition_reasoning/` |
| Memory | Snapshots, the memory derivation DAG, and load and store resolution | fast | `src/kernel/primitives/cell_store.rs`, `src/kernel/reasoning/memory_resolution.rs`, `src/kernel/memory_provenance.rs` |
| Resources | Ownership, views, loans, folds, and separation | fast | `src/kernel/primitives/resource_algebra.rs`, `src/kernel/resource_tracker/`, `src/kernel/loans.rs` |
| Simple tactics | Apply one checked step to a persistent proof state | fast | `src/kernel/proof/object.rs`, `src/surface/proof/proof_object/`, `src/surface/proof/checked_drivers/` |
| Certificates | Check explicit arithmetic certificates and contract claims | fast | `src/kernel/proof/{integer_arithmetic,signed_arithmetic,arithmetic_special}.rs`, `src/surface/proof_certificate.rs` |
| Termination | Plan recursion heights over the call graph, then check them | fast | `src/kernel/termination.rs` |
| Smart tactics | `solve`, `step_until`, the implicit tail and its closer | slow | `src/surface/checking/{arithmetic_engine,simplex}.rs`, `src/surface/proof/{smart_closures,smart_execution,selected_arithmetic}.rs` |
| Search helpers | Fill an elided premise, fact, resource instance, or guard | slow | `src/surface/planning/proposition_search.rs`, `src/surface/proof/fixed_state_proofs/` |
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
  facts, the snapshots, or the resources, and then keeps only the entries it
  needs. This rule has no exceptions: a fast-part operation doesn't scan even
  the facts "related" to its input unless an index hands them over by key.
  Following an index from entry to entry (a chain of order facts, say) is
  allowed when each step reads only entries filed under the current key and
  the walk reads each entry at most once.

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

Operations in the fast part that scan today are listed, with the options for
each, in
the "Fast-part scans" section of [the smart-tactics roadmap item](https://github.com/clicklang/click/blob/master/roadmap/smart-tactics.md).

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
Exact fact withdrawal is test-only, for negative controls that remove a premise;
it is not a production backtracking operation. The build boundary also rejects
production references to the withdrawal entry points. Tests may pay for index
rebuilds after removing a premise; those helpers have no fast-checking guarantee.
`tests/search_boundary.rs` checks rejected dependencies, aliases, method
references, macro tokens, extra diagnostic scans, and capability privacy.

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
nonempty witness or singleton symbolic supplier. Designation/opaque-extent
fallback comparisons use a singleton direct alias after indexed equality fails.
Framed pointer-value recovery requires one address alias and one full-pointer
source in that address bucket; multiple snapshots do not authorize a hidden
source search. Complete-read, snapshot, designation and extent checks still
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
selected source may have another block spelling: checking aligns the two
supplied addresses through the graph and retains bounds, lifetime and
structural-distinctness checks. Preserve existing same-block endpoint expressions
unless the addresses are already equal; coordinate projection must not obscure
their stated bounds. Other spellings require search permission.
The build boundary rejects alias enumeration in these migrated view queries.

Condition-fact queries use the maintained truth index and singleton canonical
shape/variable buckets. Atomic memory-order queries use indexed truth for both
orientations, retaining the comparison carrier; compound memory queries still
require their canonical key or an explicit spelling. No query enumerates scalar
classes to select a premise. Other condition-side bucket helpers remain audit
targets.

Read-validity evidence uses exact typed/snapshot membership and singleton
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

Writing a search out requires every fact it cites or proves to have a Click
spelling; [Spellability](spellability.md) states that rule. A search that
can't be written out as explicit tactics isn't allowed in the
slow part either: then there's no way to remove its cost, which makes it fast
part, and fast part may not search. [Smart and simple
tactics](../concepts/smart-and-simple-tactics.md) defines the tactic classes
and the target set of four smart tactics.

## Design check

Answer these before proposing a verifier change that adds work.

1. **Which part does it change?** Name it from the table above.
2. **Fast or slow?** If it adds reasoning to a fast part, ask first whether
   it could be a slow-part search instead: a new strategy in `solve` or
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
   graph ([fact-stable lowering](spellability.md#lowering-is-fact-stable)).
   Run `scripts/fact-stability.sh` before and after, and add no new
   differences.
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
| memory derivation DAG, snapshot, cell store | How memory states and their cells are stored and related | Memory (fast) |
| DAG bridging | Relating a load at one snapshot to cells of an earlier one | Memory (fast) |
| carriers, compositions, separation | How owned resources and their disjointness are represented | Resources (fast) |
| fold, unfold, views, loans | Building, opening, and borrowing resources | Resources (fast) |
| proof object, proof step | The persistent proof state and one checked change to it | Simple tactics (fast) |
| certificate | An explicit derivation the kernel checks without search | Certificates (fast) |
| planner (signed, `Integer` affine, special, simplex refutation) | Chooses an arithmetic certificate | Smart tactics (slow) |
| selected-premise arithmetic | `solve`'s choice of the facts and type ranges arithmetic refutes an arithmetic goal from | Smart tactics (slow) |
| rewrite search, equality chain | `solve`'s search for rewrites that close a goal | Smart tactics (slow) |
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
and snapshot checks. Ambiguity declines; it does not enumerate the endpoint
bucket. For a transported read's constant value, prove the current read equals
the saved read first, then normalize using that equality and the saved value.
This explicitly supplies the connection that an ambiguous constant endpoint
bucket cannot choose. Build-time boundary checks reject the removed enumeration routes, and
`condition_buckets` scaling regressions grow both related and unrelated state.
Other remaining checking walks are tracked in `roadmap/smart-tactics.md`.

### Written literal and ownership queries

`direct_scalar_constant` accepts a literal or an exact stated Int32/UInt32
literal equality in either orientation. The existing scalar-class summary
nominates its value; ambiguous summaries decline. A chain or arithmetic folding
alone does not supply the written premise: derive and state the endpoint
literal equality explicitly. Checking reads at most four exact premise keys,
without traversing equality evidence edges.

Store ownership footprint lookup uses only the additive bases written in the
access. It does not enumerate their pointer alias classes. When a resource is
owned under another spelling, state the alias and separation explicitly and
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
exact signed-order facts supply direct evidence. Private-local separation reads
the addressability registry and an indexed equality-graph block coordinate;
it does not enumerate aliases. A miss forgets the cached value. The boundary
rejects general resolution, range search, alias enumeration and order-path walks
in this helper. Growing same-block separation buckets leave cold and repeated
miss work unchanged, while written index disequality still respects access
widths. Byte-gap eligibility also reads only an exact stated signed order;
it does not follow recorded order chains. State the endpoint inequality with
an explicit proof when needed.

Store preservation of compact runs uses constant byte geometry or the cached
signed interval of the written index. It forgets the entire possible write
window as an interval, including for runs whose values are symbolic loads or
copies. The existing bounded ownership selector also handles a run as one
complete byte footprint. One explicitly stated separation selected by the
run/write address anchors can likewise retain the whole run, provided both
complete byte footprints fit.
The lookup inspects at most two candidates and declines an ambiguous bucket.
An otherwise unplaced write forgets the whole run. It does not enumerate
logical slots or search separation-fact buckets. Initialization records and immutable
source history remain available; explicit separation and `transport` recover
selected values, as in
`mdtests/store_geometry_uses_explicit_order_and_transport.md`. Scaling tests
grow order chains, separation buckets and logical run lengths independently;
the build boundary rejects the removed search and per-slot routes.

An explicit loop read frame can select a flat range withheld from the loop
body by the checked ownership partition. The loop history retains that
persistent frame even when a conditional collection's conservative mutable
footprint overlaps it. Selection reuses the indexed kept-range query with no
composite expansion; a singleton covering range must include the entire read.
A scalar cached prefix does not preserve a complete pointer. Distinct retained
frames have distinct havoc identities, and a later overlapping store still
invalidates the read. This adds no implicit store-preservation search.
