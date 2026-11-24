# Raise-lower principle

Every proof-visible `KernelProposition`, whether it is a fact or a goal,
must raise to a whole `SurfaceProposition` that lowers back to the same
checked proposition in the same proof context, up to renaming bound
variables.

```text
KernelProposition → SurfaceProposition → same KernelProposition
```

This includes the logical structure, binder scopes, guards, program points,
and the identities of all terms the proposition contains. For example, raising
the operands of a read under `forall` preserves that read as part of the
quantified claim. The complete round trip also preserves the quantifier and
its scope. The `KernelTerm` to `SurfaceTerm` round trip applies to those
operands in their enclosing scopes and to standalone terms that expansion
writes directly, such as witnesses or call arguments.

Raising preserves types, bindings, value identity, and snapshot identity. It
uses names and origins retained where values are introduced; it does not
try historical states until a candidate happens to lower correctly. Printing
then converts that Surface AST to source text. Printing chooses syntax and
layout; it does not discover names or reconstruct missing semantic information.

Every fact a proof holds and every goal it focuses must satisfy this
principle. This is a design rule, not a presentation goal.

## Why the rule exists

`click expand` replaces each smart step with the simple steps a person could
have written ([Expansion](../concepts/expansion.md)), and the [slow-part
rule](verifier-design.md#the-slow-part-rule) admits a search only when its
result can be written out that way. A simple step names what it cites and what
it proves: a `have`, a `using { ... }` premise, a witness, an `instantiate`
argument. So every fact a smart step relies on, and every goal it leaves, must
be writable, or the smart step cannot be expanded.

When a fact has no Surface form, today's code works around it rather than failing:

- a smart tactic declines a route whose premise it cannot cite, even though
  the kernel holds the premise (`close()`, its arithmetic bridges, the implicit
  closer), so a provable goal fails as a bounded miss;
- a recorded Surface form that does not check is dropped, so later steps cannot
  cite the fact;
- a diagnostic prints a placeholder (`<unnamed A>`, `<pointer A>`,
  `<state A>`) or an angle-bracket description in place of the fact;
- expansion refuses its own output when a placeholder leaks into it.

None of these is unsound, since every cited Surface form is lowered again and
checked. Each one costs completeness, expansion, or a readable report.

## Proof-visible program structure

The proof-visible program tree follows the target-language source. Build its
statement hierarchy and local declarations from the statements and declarations
the author wrote. Preserve their identity, order, and nesting through lowering.
Frontends may introduce typed temporaries and execution steps to model the
source's behavior. Retain the source construct responsible for each generated
operation and attribute the operation to that construct in the execution layout.
Reserve source statement selectors and local names for written constructs.

For example, a C bit-field update such as `p->delta++` is one source statement.
Its execution saves a value and may perform several byte stores. A proof can
distinguish those operations through the statement's existing atomic region
selectors. A diagnostic points to the written update and identifies the
operation that failed. [Program regions and points](../reference/language/index.md#at)

Review frontend and lowering changes against these checks.

- Statement selectors still resolve to the same written constructs. Changes
  to the internal step sequence leave source statement numbering and nesting
  intact.
- A failure in a generated operation identifies the source responsible for
  it and describes the operation in terms of that source.
- `click expand` emits source-backed selectors and names. The expanded proof
  replays with implicit solving disabled.

## The rule

- **Raise by construction, not by search.** A fact's Surface form follows from
  the fact and the names in scope. Code must not search a list of strategies
  for a Surface form and fall back to a placeholder, to another renderer, to
  `None`, or to dropping the fact.
- **Name a value where it is introduced.** A step that introduces a fresh
  value or memory state (a call result, a havoc, an allocation) gives it a
  name from its origin at that point. A fact names only memories a recorded
  point holds; a memory between recorded points has no name and is a defect
  to fix where it is made, not one to name. Do not recover a name later from whatever locals happen to hold the
  value. A non-void call's result is `<region>.result`, including calls whose
  source discards the return value. The checked call transition retains the
  exact returned value, and its exit records it by region in
  `RecordedStates::call_results`. Stored call results and named theorem bindings
  retain their `ExecutionValue` producer in immutable `RetainedProgramValue`
  carriers: existing shared roots survive region, state and argument handoffs;
  explicit native inputs retain their syntax contract. Selected compatibility
  readers borrow native output through the existing root-owned cache. No
  ambient binding map is exported. Lowering reads the selected value directly;
  integer and Boolean synthesis uses a reverse term index, and algebraic
  synthesis (a Rust enum a call returned) an index from the value to the
  first call that returned it (`algebraic_call_results`). Replacing or removing
  the recorded exit replaces or removes its result name too. A step's result
  is also named from the state that holds it (`ExecutionState::step_results`, by step
  number; `SourceExecutionLayout::step_region` maps the number to its step).
  A postfix update's result, the value it replaced, is
  `at(<its region>.entry, x)`.
  A region is raised by its statement as written. A C statement carries its
  site. Rust's lowering builds its kernel body itself, so it hands the layout
  the statement each region comes from: `moves::Sited` builds each lowered
  statement with one source site per region, in the layout's own preorder.
  The sites come from the MIR `Site` statements the Charon import places,
  each the innermost `syn` statement holding the MIR's span
  (`source_statements.rs`). The layout refuses a function whose region count
  differs from its sites' count, rather than guess.
  Source-layout result locals preserve allocation naming.
  A call that copies a by-value aggregate argument into its parameter object
  names that copy `<region>.parameter(name)`: the call producer hands back
  the memory just after the copies, with only those parameters bound
  (`kernel::CallParameters`), and the step records it as the region's
  parameter point (`ProgramPointKind::Parameters`). The callee's contract
  reads the copy there, so a step that prepares the call exposes that point at
  its pre-state while it proves the call's requirements, and the source-backed
  requirement Surface form substitutes `R.parameter(name)` for the parameter.
  Reads through it are resolved from the recorded layout when lowered.
  In the function's own proof the parameter is the input itself: the entry
  declares its object holding its own entry values
  (`kernel::program_function_input_objects_state`), so `p.f` names the value and
  the body's private copy and its result are computed from that name
  (`mdtests/a_by_value_struct_parameter_is_one_value_in_its_own_proof.md`).
  A heap allocation keeps its nullable return value as `<region>.result` and
  names its success identity as `<region>.allocation`. The producer reserves
  both identities before the null check. The allocation exit indexes the heap
  pointer in `RecordedStates::allocation_results`; raising it uses that name
  after reassignment or `free`. The name grants no allocation success, liveness,
  or read authority. Its value is constructed from the producer's recorded
  pending allocation, without facts or a history scan. The index is scoped with
  recorded states and removes a name when its exit is replaced or removed.
  A loop head mints its pass count `K` fresh; the loop's phases raise it
  `iterations` (kernel placeholder `LOOP_ITERATIONS_VARIABLE`, bound per phase
  by `LoopIterationsScope`), and each path past the loop carries it on its
  correspondence metadata to the exit, which records it by loop in
  `RecordedStates::loop_iterations` as an Integer root, with a reverse index from the variable:
  it is raised `loop(i).iterations` in one lookup.
  Recorded points index each integer value, and each pointer's block, by the
  point and the local it was first given to (`RecordedStates::value_points`
  and `pointer_points`, filled from the locals each recorded state changed),
  and each symbolic integer or algebraic model-field value by the point whose
  resource instance first held it (`field_points`, filled from the instances each state changed), and
  each integer a memory cell came to hold by the point that recorded it there
  (`cell_points`, filled from the cells each memory changed). The structural
  raiser writes `at(point, ...)` from these indexes for a value no nearer
  state names. A read names the canonical projection of the memory it
  reads (`reasoning::memory_resolution`); the kernel records the memory each
  projection was built from when it builds it (`load_projection_source`), so
  the read is raised at the point recording that source, in one lookup.
  The raiser never tries recorded states, nearby memories or candidate
  forms in turn.
  A local that keeps one value in memory, a borrowed Rust enum or
  type-parameter local (`AggregateLayout::holding_value`), is named by its
  own name: `o` lowers to the read of its object at the point it was last
  written (`ExecutionState::held_local_value`), never to a value a store left there,
  and that read raises `o`, or `at(point, o)` at the recorded point whose
  memory reads it.
- **Every fact kind has syntax.** A kernel fact that a proof state can hold
  has a Surface form. Adding a kernel fact or term form includes adding its
  Surface form and its Surface form, in the same change.
- **A Surface form lowers back to its fact.** The Surface form of a fact, lowered in
  the same context, is that fact.
- **A refined goal keeps a Surface form.** A step that refines a goal carries the
  goal's written Surface form forward where it can, as `rewrite` rewrites it, and
  otherwise raises the new kernel goal (`Proof::raised_goal`). Smart search
  also retains the refined goal's Surface form: it reconstructs from source names,
  the current and entry states, and indexed recorded points, then checks the
  exact structural lowering. It does not run premise-raising search or scan
  alternative local aliases for this presentation. A named goal remains an
  outstanding obligation; producing its Surface form grants no proof authority.

A fact that exists only inside one kernel step, and never becomes a proof
state's fact or goal, needs no Surface form.

## Shared term migration

`SurfaceTerm` is the source expression AST; `ContractExpression` remains a
compatibility alias. `KernelTerm` is an immutable typed expression DAG whose
arithmetic and call operands are themselves `KernelTerm`s. Its structural
identity is independent of equality-graph classes: constructing `1 + 1`
does not construct `2`. Nodes retain their result type, and checked arithmetic
constructors reject the wrong operand type or arity.

Specification-side Integer arithmetic (`lower_integer_arithmetic_proposition`)
and ordinary Integer arithmetic on existing values construct the shared tree.
Ordinary negation, addition, subtraction, multiplication, and constant-nonzero-
divisor quotient/remainder use the same constructor. Expressions still requiring
evaluation retain their `SpecIntegerExpression` forms and scoped obligations;
a symbolic divisor still needs its nonzero check. Integer arithmetic and
pure-call raising consume the shared tree through `raise_kernel_term`. The existing
checker still receives `IntegerTerm` through a lossless, memoized export;
other producers enter through the memoized import. Neither bridge reads facts
or simplifies terms. These are migration boundaries, not a second semantics.
Machine-integer arguments now import into typed shared literal, variable,
binary, complement and explicit-cast nodes. The result type and operator
format are distinct: a `uint32` result may contain a sign-free `int32` word
operation. Literal payload tags survive exactly. Export builds the explicit
boxed checker output once, without cloning every intermediate subtree.
Ordinary specification evaluation constructs shared nodes directly for
same-format 32/64-bit signed and unsigned addition, subtraction, multiplication,
division, remainder and shifts over already available values. Children stay
shared until the final native `SpecExpressionPath::value` export. Definedness
obligations retain those same operands: signed range and division-overflow
conditions, C-defined division's nonzero divisor, and shift count/result bounds.
Total specification division keeps its existing zero-divisor semantics. The
evaluator retains its existing literal-only evaluation; the shared constructor
itself does not fold. A mixed-format or deferred operand retains the legacy
evaluator, and one rejected preparation disables further attempts inside that
selected tree.

Integer conditionals now retain their condition and branches as common children.
Raising visits common machine arithmetic, casts, observations, Boolean
comparisons/conditionals and Integer conditionals directly. Unmigrated payloads
still cross explicit legacy boundaries; native result carriers, folds, full
pointer/algebraic payloads and consolidation of general lowering remain open.
See the live inventories in `roadmap/kernel-term-split.md`.
One same-format `int32`/`int64` addition, subtraction or multiplication over
two available values also constructs a shared node, accompanied by the existing
ordinary-proposition range obligation. Literal evaluation and held-resource
domain metadata remain evaluator responsibilities. When the exact arithmetic
result is one machine observation (for example, the domain calculation for
`x + 0`), its source type alone can establish representability in a containing
type. This root-type rule never walks the operand or folds the machine value.
Conjoining domain conditions then drops literal truths only; symbolic conditions go to ordinary obligation discharge,
without invoking the proof checker while building the domain. Nested signed expressions
retain the legacy evaluator while obligation producers and checker views migrate.
`IntegerTerm::Machine` now stores an arithmetic operand as a `KernelTerm`
handle when its leaves are literals or variables and its nodes are machine
unary/binary operations. Observation interning keys this fragment by format and
child identity. The old boxed entry point imports the same identities and
retains its supplied boxed input. Imports are reused within one verification;
session-scoped bookkeeping prevents earlier warm caches from changing later
verification work. Its arithmetic importer stops at conversion/opaque leaves
without traversing them. Neither Integer bridging nor root value-reading
materializes operands created directly from shared nodes. The old
`value()` boundary materializes one boxed tree lazily. Conversions and opaque
payloads retain exact legacy storage until their checker views migrate; cached
eligibility depends only on immediate children, never facts. This storage step
does not yet permit nested signed production: consumers that request every
prefix through `value()` would still expand those prefixes repeatedly. Other partial operators also remain on
legacy producers with separate obligations. C execution has not migrated. Shifts use the
same shared binary nodes: lowering has already converted a count to the
left operand's carrier width, and the bridge preserves that explicit conversion
without reinterpreting it from the result's signedness. Widening Surface forms explicitly retain the source `int32`/`uint32`
interpretation: zero-extending signed `x` prints as `(x as uint32) as uint64`,
so lowering cannot replace zero extension with sign extension. Pointer-carrying
integers retain their complete metadata, even though their C type is numeric.
The six specialized 32/64-bit extensions and low-word conversions also use
shared cast nodes. A transitional encoding tag distinguishes their exact
legacy constructors from a generic cast with the same formats; import/export
never silently normalizes one into another. Low-word extraction interprets
its operand as unsigned bits, independent of the source C signedness.
Machine raising currently uses one exact export to the existing raiser.
Integer bridge shortcuts are memoized per verification session (and reset when
restoring a reusable session), while the shared term identities remain stable.
Retaining a converted term across runs must not change a later run's deterministic
work count. Within a session, repeated conversions still reuse the cached bridge.

Mathematical observations of machine values (`to_integer`) now have a shared
`MachineObservation` node with the interpretation format and machine operand.
Signed and unsigned interpretations remain distinct. Raising retains the observation's interpretation inside any program point selector;
a local's name must not silently choose a different signedness. Narrow values retain their
existing load/conversion Surface form: adding another narrowing or promotion cast
changes the structural observation, particularly under quantified binders.
Observation casts use `SurfaceTerm::CUnary` with the Surface operand retained;
projecting a resource field or scoped name into a C fragment loses its binding. The checker bridge reconstructs
the exact `IntegerTerm::Machine` payload without folding arithmetic.
Mathematical-Integer-to-machine conversions use an `IntegerToMachine` shared
node with an Integer operand and explicit destination format. Raising uses the
existing `to_int32`, `to_uint64`, etc. calls; exporting reconstructs the original
conversion without evaluating the operand or consulting range facts.
Wide symbolic cast chains retain their intermediate nodes. Collapsing
`(x as int128) as int64` used to create a generic `int32`-to-`int64` cast,
while its direct Surface form lowered to the `Int64From32` Surface form of `Cast`. Retaining the chain
restores the round trip. The existing 32-bit word-cast conventions remain.
The raiser now handles explicit wide casts and wide literal payloads.
Cast-composition equalities, including 128-bit intermediates, are maintained
by the equality graph's indexed machine relations. A full-width source's
conversion through a no-narrower intermediate can be related to its direct
modular conversion; a lossy intermediate does not restore the original value.
No stored cast node is replaced by that equality.
The `Legacy` leaf retains complete unmigrated values, including pointer
metadata, array states, and scoped binders. Those families do not yet have
unified constructors or total raising. Boolean-to-machine conversions
now have a shared `BoolCast` node with a logical `Bool` child. Boolean literals,
variables, machine comparisons, equality, conditionals and calls have structural
nodes. Mathematical-Integer comparisons use `IntegerCompare`, retaining all six
operators and both typed Integer operands. A greater-than comparison is not
rewritten as a swapped less-than comparison, and disequality remains explicit.
Native signed division and remainder now generate ordinary domain propositions:
`b != 0` and `(a != MIN or b != -1)`. The conjunction is also the premise of the
int32 remainder-to-Integer theorem. Specification evaluation retains the complete conjunction as one operation
domain, and C execution records the ordinary exclusion on its
normal branch and the two exceptional equalities on its undefined branch.
Signed addition, subtraction, and multiplication use the exact mathematical
result bounded by the format minimum and maximum. Unary negation uses
subtraction from zero. C shifts conjoin the count bounds and, for signed left
shift, a nonnegative operand and representable result; Rust shifts require
only the count bounds. Unsigned wrapping operations have no overflow debt.
The supported 128-bit operators also retain one complete ordinary domain.
Only literal truths disappear during domain construction; symbolic conditions
remain for ordinary obligation discharge. Assumed facts never change the term.
Existing interval rules may interpret these propositions through private
overflow queries, but generated domain facts, theorem statements, and
certificate conclusions use ordinary propositions. Symbolic machine operations
keep their nodes even for algebraic identities such as `(x + 1) - 1`; the
comparison graph can identify equal words without changing those terms.
Operation-identity certificates preserve explicit operands and establish
operand identities before the outer operation, independent of discovery order.
Other conditions retain an exact `LegacyBool` payload. Import/export does
not use condition fact equality: signed and unsigned equality comparisons keep
their original format even where the fact store identifies them. Raising a
conversion writes `b as int32` (or its destination type), retaining the Surface
operand through `CUnary`. Legacy call
arguments retain their producer identity and exact payload: semantic pointer
equality must not select a different auxiliary qualifier or evidence record.
This change
does not settle the C pointer field design or close the remaining census misses.

Shared nodes use shallow child identities, cached key hashes, and bounded
interner cleanup. Converted Integer nodes cache their common term; reverse
links are weak to avoid reference cycles. Repeated lowering reuses those
links rather than revisiting the growing expression behind a binding.
Bridge tests grow shared DAGs and unrelated nodes separately; surface tests
check arithmetic and nested calls through raising, printing, parsing, and
ordinary structural lowering. The certificate operand test compares the
resulting `KernelTerm` identity directly. Subsequent migrations should remove
legacy leaves and adapters family by family rather than adding parallel trees.

A derived signed range for a native `uint32` value retains the conversion
`x as int32`: a signed comparison of the raw unsigned term would raise with
that conversion and lower to a different term. When the unsigned operand was
already converted from an `int32` source, the range instead names that signed
source. Admission and decision use the same structural rule; this does not
change lowering or erase conversions elsewhere. The simple `close()` proofs
in [the checked range fixture](https://github.com/clicklang/click/blob/master/mdtests/unsigned_small_bound_signed_facts_round_trip.md)
exercise the exact derived facts.

## Kernel authority

Some kernel propositions are checked context, not proof-state facts: a
resource composition (resources held together) and a predicate with no Click
name, such as subobject coverage or a volatile event. The kernel stores,
transports, and validates them with every other fact, so a step's delta still
justifies each one. No surface view presents or cites them: the census,
proof traces, diagnostics, and premise raising all skip them, and a closing
step reads them from its context. One classification,
`Proposition::is_kernel_authority`, decides membership; code must not
special-case a composition or a `__click_` name elsewhere.

`held`, `same_allocation`, and contract facts are not authority even though the
kernel names them under `__click_`: `kernel::predicate_source_name` gives the
Click name that lowers to each, and the printer, synthesis, and authority
classification all read that one mapping.

The observed value carried by a volatile read event has a public Surface form even
though the event predicate remains authority: `R.read_event(i).result`. Execution
records its exact typed value in the presentation state and indexes that value
for raising. Lowering retrieves it directly without consulting equalities or
performing another load. Internal handles therefore raise as event results,
not anonymous variables.

Making a proposition kind authority is a design decision, never a way to
avoid Surface form a fact a proof could need to cite.

## The raise-lower principle

Raising turns a kernel term into Click text; lowering turns Click text into
a kernel term. Three rules relate them. Each has a target form, stronger
than what the verifier enforces today, and an audit that measures the gap.

| Rule | Target | Enforced today | Audit |
| --- | --- | --- | --- |
| Lowering undoes raising | `lower(raise(x)) == x` for every term a proof state holds, so a raised Surface form needs no checking | Required, but premise raising lowers each candidate again and drops a mismatch (`surface_lowers_to`, premise raising's `matches_kernel`) | `scripts/audit.sh raise-lower` |
| Lowering is fact-stable | Lowering reads no facts: one text, state and set of resources lower to one term | Facts may refuse the term, discharge its obligations, add side facts, or select one of several paths; they may not change the term | `scripts/audit.sh fact-stability`, `differs` lines |
| Definedness is an obligation | Lowering returns the term, its definedness obligations and its side facts; checking discharges the obligations | Ordinary arithmetic returns obligations beside the term, but lowering drops one the facts already prove, and some lowerings are refused instead of owing one | `scripts/audit.sh fact-stability`, `refused` and `paths:N` lines |

`click audit fact-stability` and `click audit raise-lower`
(`scripts/audit.sh fact-stability`, `scripts/audit.sh raise-lower`) run these
two audits over the examples and mdtests an expansion audit walks, and each
ends with one headline count of the items that fail
([`click audit`](../reference/cli/audit.md)).

The fact-stability audit reports three kinds of fact-dependent lowering.
A `differs` line breaks the enforced rule. A `refused` line is a proposition
that lowers with facts and not without them; a `paths:N` line is one the
facts selected from `N` fact-free paths. Both are allowed today, and both
are where the facts, not an obligation, decide definedness. The target
form removes them.

The raise-lower audit raises each fact a checked step adds, and the goal
it leaves focused, as goal presentation does
(`Proof::structural_proposition_candidate`: the step's fixed state, its
entry state and the path's recorded points, so `at(point, ..)`, `old(..)`
and `<call>.result` forms are available), lowers that Surface form again,
and compares the complete proposition up to bound-variable renaming. It records
`same`, `polarity` (an equivalent comparison that changed representation),
`differs`, `unlowered`,
`unraised`, or `no-state`. It measures the raiser alone, not premise raising,
which searches recorded Surface forms first and keeps only one that lowers
back. It observes the steps the [census](#measuring-the-gap) does; a
fact a `have` publishes to its enclosing proof is not among them.

Baseline (2026-11-16, ordinary mdtest corpus, both runs passing):

- Fact stability: 0 `differs`, 0 `paths:N`, 371 `refused` lines in 19
  fixtures; 338 of them come from
  `mutex_resource_quantity_requires_conservation` (`uint32` comparisons).
- Round trip (2026-11-17, after the audit raised with recorded points and
  the entry state, pointer call results were indexed, and closed literal
  comparisons stopped folding): 55,575 records. Of the 16,046 Surface forms
  the raiser produced, 13,780 were `same`, 698 `polarity`, 1,201 `differs`
  and 367 `unlowered`; 4,318 terms were `unraised` and 35,211 had
  `no-state` (mostly termination predicates). Pointer comparisons account
  for 367 of the `differs`: pointer reads named by the memory they were read
  in rather than their version point, addresses raised to a placeholder, and
  pointer values with no recorded origin. Before the audit used recorded
  points (2026-11-16) it reported 9,343 `same` of 54,642 records, because no
  `at(point, ..)` or `old(..)` form was available to it. Other recurring
  `differs` shapes: a C parameter named `result` raised as Click's `result`
  (`old(*result) == 7` raised as `result->value == 7`, which at function
  exit lowers to the returned `next`); a reflexive comparison lowering folds
  (`p == p` to `true`, 75 records); casts raised differently on the two
  sides of an equality; and reads raised at a neighbouring program point.

Baseline (2026-11-20, ordinary mdtest corpus, both runs passing):
fact stability 0 `differs`, 0 `paths:N`, 129 `refused`; round trip 76,957
records, of which 34,508 `same`, 932 `polarity`, 1,076 `differs`, 338
`unlowered`, 1,650 `unraised` and 38,453 `no-state`. The two runs take about
18 minutes together.

The nightly workflow's `raise-lower-audit` and `fact-stability-audit` jobs
run them (`scripts/check.sh --audit <audit>`). A fact-stability `differs` or `paths:N` line
fails the nightly report, since it breaks the enforced rule. The round trip
is tracked instead: the report lists each outcome's count beside the
previous night's and flags a rise in any count but `same` and `checked`
([Nightly report](testing.md#nightly-report)).

## Lowering is structural

A lowered term has the structure of the surface text it lowers: each
operator, call, and read lowers to the corresponding kernel node over the
lowerings of its operands. Lowering never replaces a term by a different
term known to equal it, whether the equality comes from a fact or from a
value a store left in memory. Lowering `a[i]` to `5` because `a[i] = 5` was
stored, or `p->next` to `q` because `q` was stored there, makes the term a
proof states differ from the term it proves: a goal `X == Y` is discharged
as `lower(raise(X)) == Y`, and rewriting tactics move a term that is not
the one the text names.

- Required: `lower(raise(x)) == x` for every kernel term a proof state
  holds.
- Allowed: `raise(lower(s))` may normalize surface syntax, collapsing
  Surface forms of one structure; the kernel need not produce every surface
  form. In particular `at(point, expression)` can raise at any program point
  whose recorded state selects the same version point for the read. Distinct
  program points may lower to the same read; raising picks one of them.
- Allowed: identifying two places whose values are structurally equal by a
  fact-free walk, which names one place twice rather than substituting a
  value. The version walk below is that case.
- Not allowed: substituting a known-equal term, constant-folding a
  comparison the facts decide, dropping a decided guard or disjunct, or
  choosing a term by known origin. Equalities stay in the equality graph
  and the comparison form, which every check consults.

Lowering never folds a comparison of two literals.

- Closed native comparisons at 8, 16, 32, and 64 bits, order and equality
  alike, retain their comparison node, format, and literal operands:
  `1u64 == 0u64` lowers to that comparison, not to `false`. A closed 64-bit
  equality is filed at the native `Int64` word equality format, with its
  literal operand payloads, and is decided by its bits.
- A comparison of the same variable at 32/64 bits retains its comparison
  node: recognition compares the two variable IDs, without consulting facts
  or walking expression trees.
- A contract `p == p` (or `p != p`) of one non-null pointer value retains a
  `AddressEqual` node rather than folding to `true` (`false`), and
  `address(p) == address(p)` retains its `int64` address-word comparison.
  Lowering and the producers whose results must match a lowered goal
  (`preserve`) build the pointer equality with
  `ConditionTerm::logical_pointer_equal`. A pointer equality raises as
  contract `p == q`, which lowers back to it; the weaker
  `address(p) == address(q)` is the address-word equality a C comparison
  states (`design/pointer-subobject-bounds.md`, Phase B). A `AddressEqual`
  between two pointer values of different provenance has no Surface form yet:
  `p == q` lowers to `PointerEqual` for them, and the round trip refuses.
- A comparison of two `bool` literals, `true == false`, retains a
  `BoolEqual` of the two constants.
- A comparison of same-width floating-point literals retains its operator,
  width, and both bit patterns. Checking decides the result with IEEE
  semantics, including signed zero and unordered NaN comparisons.
- A logical Boolean comparison with identical operands also retains its
  `BoolEqual`. `==` and `!=` record opposite polarities on that node.
  The checker decides reflexivity, including when the comparison is a guard.
- A written `true` or `false` is a literal proposition, not `literal ==
  true`: it lowers directly to the constant condition
  (`SpecProposition::Truth`). The raiser raises a constant condition to the
  same literal, so `false` round-trips without a comparison.

Closed float comparisons and classifications retain a directly written
negation or binary operation over same-width literal operands. Checking
computes each operation at its written IEEE precision. Float comparisons
retain their polarity for NaN, including negated order comparisons.

Checking decides a closed condition from its literal roots with
`machine_integer::comparison::closed_condition_value`, including when exact
rewriting removed the last variable before the comparison was printed. It
does so in exact matching through the comparison form, including closed
comparisons nested under connectives and binders (so `contradiction(1 == 0)`
matches a held `false`), in requirement matching, `normalize`, and
assumption-free normalization. The fact store records a closed comparison
that holds without indexing it. A closed goal is false or true whatever the
facts, so `close()` treats a false one like the goal `false` and refutes the
path. Regressions: `mdtests/closed_machine_order_comparisons.md`,
`mdtests/closed_machine_equality_comparisons.md`,
`mdtests/an_infeasible_path_with_a_closed_order_goal_closes.md`, and the
`closed_*` and `a_constant_condition_raises_*` unit tests in
`surface::proof::surface_synthesis`. Literal arithmetic evaluation is
unchanged, and the shared comparison constructors used by checking still
fold.

Direct logical comparisons also retain a closed `if` over simple
`Integer` or algebraic arms. The arms can be literals or bound values, and
algebraic arms can be constructors with simple fields. Checking reads the
selected arm, and admission of a comparison makes the equivalent selected
comparison available through the existing fact indexes. Partial and
state-dependent operands use the existing evaluation paths.

Machine conditionals with closed 32/64-bit order guards, closed 64-bit equality
guards, or same-variable 32/64-bit comparison guards retain their `if` node and
guard during logical lowering. Their arm domains remain guarded, including
unselected reads and invalid shifts. Checking selects the arm when needed.
The comparison boundary recognizes fixed-size native conditionals, including
one immediate conditional in either arm or on either side of a machine
comparison guard. A guard can be a Boolean variable, an
equality of two Boolean variables, or a 32/64-bit comparison. Machine comparison
operands and innermost arms can be literal or variable leaves, one bitwise
operation (`&`, `|`, `^`, `~`)
over such leaves, a right shift or unsigned left shift by an in-range literal
count or with two variable operands, a sum, difference, or product over two variables, or an unsigned one over a
variable and a literal,
a quotient or remainder of a variable by a nonzero literal (excluding signed `-1`),
an unsigned quotient or remainder over two variables,
a signedness cast of one variable, or a 32-to-64-bit widening or 64-to-32-bit
low-word cast of a leaf. A signed
comparison spells the low-word cast with its signed destination. Wide equality retains an unsigned
widening in its original type, even though the equality is filed as `Int64`.
The comparison or conditional result type can identify a `uint32` operation
whose node carries the shared 32-bit word encoding.
Standalone comparisons also recognize the bounded bitwise and shift operands.
Even intrinsically decided guards in these forms retain their conditional;
checking selects the arm. The
reader inspects only the operator and its immediate leaves. Negated Boolean
variables use the same guard with swapped arms. This preserves the comparison
family without exporting arithmetic DAGs or using ambient facts to select an arm.
A Boolean or 32/64-bit machine conditional can retain identical arms after an
exact rewrite. Logical lowering keeps that conditional when its guard is
representable and symbolic. Checking can then use the common value.
Closed machine equality guards keep the comparison and both arms when
the result is a retained scalar. A 32-bit equality retains a conditional
whose arms have the same 32-bit or 64-bit machine integer type. Introducing
an Integer binder preserves that conditional. Literal Boolean guards keep
their selected-arm behavior.

Checked rewriting reconstructs native 32-bit comparisons with word-form literal
operands, matching logical lowering even when selecting a conditional's unsigned
literal arm. This touches only operand roots, preserves nested arithmetic and the
comparison node, and leaves truth evaluation to checking.

Generated comparison operands that are negative `int64` literals keep an explicit
`as int64` cast, including under `old` and `at`. Their printed unary minus would
otherwise reparse as mathematical Integer arithmetic and change the comparison
family. Authored and diagnostic forms keep the ordinary negative literal.

Closed narrow native comparisons raise both operands with explicit `int8`,
`uint8`, `int16`, or `uint16` casts. This preserves their format after a checked rewrite
exposes literal operands: converting those literals to mathematical Integer
observations would erase the width and signedness. Closed narrow logical orders retain that native format. Symbolic comparisons
keep their existing observation form, and mixed-format comparisons and
executed C keep their existing integer promotions. Literal order truth is checked without
changing the retained comparison, including after quantified substitution.

Checked machine equality rewriting evaluates a 32-bit division, remainder, or right
shift when its operands are literals, using logical
arithmetic's existing literal constructor. Native and shared operands follow
the same rule. Symbolic instances of these operations and exact
Integer-congruence payloads retain their syntax; division by zero, signed
division overflow, and invalid shifts
remain opaque instead of acquiring an invented value.

Explicit `Integer` conversions such as `to_int32(7)` retain their destination
and operand in logical lowering. A literal must fit its destination. Checking
may read the converted value from those two roots without changing the term.

Logical object-pointer reads now retain their version names, including when
memory stores a complete pointer at the cell. The read's complete stored value
is related through `EqualityGraph::register_logical_read_values` and the
producer's read equations; its address, bounds, and provenance are not folded
into the lowered term. The cached-prefix route also excludes logical reads
from fact-supported recovery, even outside specification scope.

The legacy stored-pointer fold (`complete_pointer_read_value`) remains only
for C program reads outside specification scope
(`kernel::eval::memory_loads`); logical reads and specification-scope C
expressions retain the read. C evaluation computes with stored values, as
[a read names its version point](#a-read-names-its-version-point) describes.

## Lowering is fact-stable

Facts may decide whether lowering succeeds, discharge its obligations, and
add side facts beside its term. They never change the term: when a
proposition lowers both under facts and under no facts, the two terms are
the same up to the names of bound variables. A lowering that rewrites
through a fact, `f(a)` to `g(b)` because `f(a) == g(b)` is known, yields a
term that another context's lowering of the same text does not reach: `a ==
c` then no longer gives `f(a) == f(c)` by rewriting, and the fact holding
it has no Surface form. Equalities belong to the equality graph, which every
check consults; they are not folded into terms.

The rule is about facts, not state. A term may depend on the program point,
the memory, and the resources held there; two contexts holding the same
resources under different facts must produce the same term. A memory read
is named by the address it was written with and the state of the cell or
resource it reads, so a write to a separately owned cell leaves it alone.
A read whose cell is found only through a fact, such as reading `a[k]`
while owning `a[i]`, which needs `k == i`, stays a read of the region's
state; the equality graph relates it to the stored value. Facts may still
prove the read is permitted. A fact an unfold adds is an ordinary fact.

Array indexing observes the completed machine-integer expression exactly.
A `uint32` index always uses zero extension to the wide unsigned offset;
proven bounds cannot switch it to a signed offset. Thus `a[i + 1]` preserves
the index expression's machine arithmetic before observation, including unsigned
wraparound. The raiser structurally removes that implicit widening and writes
`a[i]` again; supported native wide indices, including Rust `usize`, also retain
bracket syntax. Range checking uses the maintained order graph to relate the
unsigned word to its exact widening, without changing the address term.
A byte offset keeps its written shape the same way: `(char *)q + i * 4` is the
byte displacement `i * 4` at stride one whatever the facts say. The pointer
arithmetic records `defined(i * 4)` when the facts decide it, and the equality
graph then joins that offset to element `i` at stride four; memory resolution
asks the same overflow question itself within the statement that forms it
(`a_word_read_through_a_byte_offset_is_the_element_read.md`).
Literal-mask bounds are recorded when the graph introduces the index node;
integer address equalities over a common exact wide stride retain full-width index
equalities. A table-read branch extends its context with its one new address
disequality before considering the next cell.

Boolean function applications, equalities, conditionals, and Boolean call
arguments raise structurally through their existing Surface syntax. Pure-theorem
premise raising uses the retained typed source state and looks up names for the
selected fact's variables, rather than rebuilding an int32-only environment.
Generic calls raise the declared source name rather than the kernel's
`::<...>` instance suffix. Typed arguments (including explicit algebraic
constructors) reconstruct the same instance when lowered. Name selection must
include variables inside opaque call arguments and both goal binders and
proof-local witnesses, respecting `intro` shadowing.
Algebraic equality inside a Boolean expression raises as an ordinary comparison.
Reflexive algebraic proposition comparisons keep both operands through
lowering. Checking decides their truth after any operand obligations are met.
A comparison also keeps a match that rebuilds its scrutinee. Checking verifies
that each arm reconstructs its constructor from its own fields in order.
Match-arm algebraic bindings retain their source names for premise synthesis,
including list tails and C type-parameter values stored in constructors. These
names are selected from existing proof bindings; no equality search reconstructs
them.
An Integer-valued match with Integer-only fields retains its scrutinee and
scoped arms even when the scrutinee is a written constructor. Goal-local
checking may select the constructor's arm and substitute its fields.
Integer equality, disequality, and standalone order comparisons retain a
direct match over a pure constructor with Integer or int32 payloads when each
arm is a literal, a payload observation, or an addition or subtraction of
those atoms. Explicit algebraic rewriting keeps that match in the comparison.
Normalization selects the arm and compares the resulting Integer values.
Pure, obligation-free algebraic-valued matches in comparisons also retain
their scrutinee and arms with a known constructor. Algebraic equality
rewriting keeps the match available for reduction during normalization.
Equality, disequality, and standalone order comparisons over a pure `int32`
match with literal arms or direct `int32` payload selections keep the machine
comparison and scoped match. Exact rewriting preserves the match.
Normalization checks the selected constructor arm using the comparison's
original machine format, and `close()` can use an available comparison
of the selected values.
A rewrite that introduces an outer Boolean negation retains lowering's truth
polarity: a false claim of `not p` is stored as a true claim of `p`. This does
not consult facts or change the Boolean term inside a larger expression.

Pure finite `int32` and `uint64` sequence comparisons preserve both
operands, including concatenation with an empty sequence. The checker
compares corresponding elements in order and distinguishes different lengths.
Admitting a sequence equality also publishes its element equalities through
the existing fact propagation path.
Pure finite membership over those same types keeps the element and the
sequence as operands of `in`. Checking proves membership from one equal
element or nonmembership from every element's disequality. Held membership
exposes the same element disjunction to `cases`, and held nonmembership
supplies the individual disequalities.

Arithmetic domains raise as ordinary comparisons and conjunctions, including
the negation of a range conjunction on an overflowing execution branch.
`defined(expression)` denotes its root operation's domain with its operands
taken as values (`kernel::spec::operation_defined`): the same kernel
conditions the whole expression's evaluation owes for that operation, so each
per-operation domain raises as `defined(l op r)` and lowers back to itself.
It does not stand for a single overflow component of division or shift. The
kernel's own `SpecProposition::Defined`, which its producers state for a term
they evaluate, is the whole evaluation domain: the conjunction of each
operation's domain, each of which raises on its own.
`mdtests/arithmetic_definedness_is_one_ordinary_domain.md` checks the ordinary
bounds in both directions for signed 32/64-bit arithmetic.

Masked uint64 tag expressions retain their full numeric term. Exact tag-bound
lookups may produce a separate equality removing the masked tag; addition also
requires the word's low bits proved clear, so no carry reaches address bits.
Those facts accompany evaluation instead of replacing its result. Explicit
ordinary arithmetic proofs must conclude the full written goal (after explicit
rewrites), rather than depend on tag removal during lowering.

`CLICK_FACT_STABILITY=<path>` lowers each checked proof proposition, and
each assumed interface proposition, again under the same policy with no
facts (`kernel::fact_stability`). It records a `differs`, `refused` or
`paths:N` line for every lowering whose fact-free result is not the same
term ([the raise-lower principle](#the-raise-lower-principle)).
`click audit fact-stability` runs every example and mdtest under it and
counts each kind; each record names its proof container. It
does not observe C execution, which may depend on facts.
Historical defects included comparisons folded using facts, pointer and aliased
reads resolved through known values, comparison kinds chosen by origin,
and decided guards dropped. Such equalities belong in checking, not in the
term lowering produces.

## A read names its version point

A Click read of an integer or object-pointer cell lowers to the read at the cell's version point,
never to the value a store left there: after `a[i] = 5`, `a[i]` lowers to the
read, not to `5` (`logical_read_names_its_version` in
`kernel::eval::memory_loads`). A read lowered to its stored value has no
Surface form of its own: no Click text lowers back to it there, so `lower(raise(x))
== x` fails for terms that contain it, and a rewrite that moves the read
(`rewrite(j, i)` on `a[j] == 5`) yields `true` instead of `a[i] == 5`
(`mdtests/a_read_of_a_stored_cell_stays_a_read.md`). The one exception is a
cell holding its own read (a materialization), which reads as that read. C
evaluation still computes with stored values: a function's `result` is the
value its statements produced.

A logical 32-bit read through a model-pointer alias keeps that same read
term. When the published footprint index selects an equal address with a
stored word, the read returns a path-local equation to that word. The
selection uses the address-class index and one exact cell lookup; it grants
no access permission and does not search other aliases or states.
`logical_read_through_an_alias_retains_the_stored_word` checks the equation,
missing-alias and changed-cell controls; its nightly scaling companion keeps
the work bounds as aliases and unrelated frames grow.

Quantified `defined` facts over a direct automatic object use that object's
producer-recorded memory version. A store to another automatic object preserves
the key; a store to the selected object changes it. The version is a persistent
map lookup, not a scan of intervening stores. Lifetime changes, unknown-address
writes and other unhandled effects keep an exact new state identity. Cache
forgetting alone preserves the version because it changes knowledge, not the
object's initialization or lifetime. This identity is for definedness facts,
not general state equality or permission to access memory.
`mdtests/local_array_quantified_definedness_survives_disjoint_store.md` covers
`close()` after a store to an unrelated local.

A scalar read handle retains its structural descriptor (memory version,
address, and read kind) in the load registry. A generated read-definition fact
uses that same handle representation as source lowering; its producer binding
retains the exact registered descriptor. A reduced cache state must not
introduce a second raw-load form into the citable equation. Cache-only records
share the unchanged-bytes identity, while actual writes still create distinct
version points. Retaining typed read evidence checks the descriptor's epoch,
address and kind by indexed lookup, independently of the Surface form.

The read-over-write authority relates a read to the stored value:
`kernel::eval::read_over_write_value` returns, for a load variable whose
state records a value at exactly its address, that value. It reads the
memory, never facts, so it holds at every program point. It enters checking
only through the comparison form (`kernel::comparison_form`): the proposition
with each read of a stored cell replaced by the value stored there.

That shared comparison form also normalizes assumption-free arithmetic
identities, including fold endpoints and the selected address of a registered
scalar read. It leaves the retained proposition and lowered operation nodes
unchanged. Read-address normalization keeps states and loaded-pointer
identities opaque and memoizes the selected registry DAG within the traversal.
Exact premise lists, signed arithmetic claims, and fold alpha keys use this
same form; they do not add tactic-specific fact searches.

- The fact stores file each fact under its comparison form too
  (`PureFactStore::with_fact`, `PureFactContext::assume_condition_once`), and an
  exact lookup also looks up the comparison form of what it looks up.
- A kernel rule that compares a stated term with one it derives compares
  their comparison forms (identity, cast identity, affine conclusions).
- `close()` tries a goal that reads stored cells over its stored values first
  (`try_stored_value_goal`), the search the goal had before reads kept their
  names, and searches over the reads only when that misses.

Code does not resolve reads anywhere else. A comparison form is a fact like
any other: a smart step that cites one raises it, and its Surface form must lower
back to it. The printer casts C arithmetic read at a state,
`at(p, a - 1) as int32`, because the parser reads arithmetic inside `at(...)`
and `old(...)` as Integer arithmetic.

A read is named by its cell's version point: the memory state the assumption-free version
walk (`resource_tracker::last_same_version_point`) selects for that cell. One
version point has one name. A cell of the canonical state that holds the cell's
own read (a materialization) names the read by that read, so a read through
an unchanged-bytes source keeps the name it had there. Two reads the kernel's
assumption-free load equality proves equal must share a name;
`kernel::duplicate_read_names::capture` audits that in tests, and the nightly
`every_mdtest_names_each_read_once` runs it over every C mdtest. Two names
remain where only facts relate the reads (a call the walk cannot cross without
a separation premise): a name cannot depend on facts, each read is raised at
its own point, and the frame fact relates them. A loop havoc is the same case:
the naming walk never crosses one, since the loop's checked footprint comes
from the proof's own annotation, so a read on either side keeps its own name
and the footprint relates them. The nightly audit lists the mdtests where the
load equality crosses such a footprint, and fails when one stops reporting. Two writes of one stored value
are two versions, related by the read-over-write authority.

## When a fact has no Surface form

Report it as a tooling defect (the `inexpressible-fact` outcome in
[tracing](../concepts/tracing.md)), and fix it by naming the value at its
introduction or by adding the Surface form. Do not add a fallback, a
placeholder, a skipped candidate, or a declining route to work around it.

## Measuring the gap

`click audit raise-lower` (`scripts/audit.sh raise-lower`) measures the
canonical raiser over every example and mdtest; see above. Tests measure
premise raising, the route `close()` takes, with the census
(`src/surface/proof/raise_lower_census.rs`): under its `capture`, each
checked step records, for every fact it adds and for the goal it leaves
focused, whether raising produces a checked Surface form. It separates steps a person wrote from
steps a smart tactic's search took: a search step needs a Surface form only when
its search succeeds and is expanded, but a written step's facts and goal may
be cited by the next written step. The census only observes; it does not
change any proof, and outside a test's capture it is off.

The census sorts a miss into one of three gaps, each with its own fix:

- **Writable but not found.** The fact has Click syntax and its operands
  have names, but the legacy raising search misses it: reflexive pointer
  equalities such as `p == p`, `viewable(p[0..1])` after an `unfold`, an
  applied theorem's conclusion such as `cd(n - 1) == 0`, and goals with no
  recorded presentation. The fix is total raising from retained origins.
- **A value with no name.** The fact mentions a value or address nothing
  names, printed `<unnamed A>` or `<pointer A>`: a callee's result, a havoc,
  an allocation. The fix is naming at introduction.
- **No syntax.** The fact's kind has no Surface form: writability, the
  memory a step may change.

The census does not count [kernel authority](#kernel-authority).
