# Spellability

Every fact a proof state holds, and every goal it focuses, has a Click
spelling: Surface Click source that a person could write in a proof and that
lowers back to that exact fact. This is a design rule, not a presentation
goal.

## Why the rule exists

`click expand` replaces each smart step with the simple steps a person could
have written ([Expansion](../concepts/expansion.md)), and the [slow-part
rule](verifier-design.md#the-slow-part-rule) admits a search only when its
result can be written out that way. A simple step names what it cites and what
it proves: a `have`, a `using { ... }` premise, a witness, an `instantiate`
argument. So every fact a smart step relies on, and every goal it leaves, must
be writable, or the smart step cannot be expanded.

When a fact has no spelling, today's code works around it rather than failing:

- a smart tactic declines a route whose premise it cannot cite, even though
  the kernel holds the premise (`solve`, its arithmetic bridges, the implicit
  closer), so a provable goal fails as a bounded miss;
- a recorded spelling that does not check is dropped, so later steps cannot
  cite the fact;
- a diagnostic prints a placeholder (`<unnamed A>`, `<pointer A>`,
  `<state A>`) or an angle-bracket description in place of the fact;
- expansion refuses its own output when a placeholder leaks into it.

None of these is unsound, since every cited spelling is lowered again and
checked. Each one costs completeness, expansion, or a readable report.

## The rule

- **Spell by construction, not by search.** A fact's spelling follows from
  the fact and the names in scope. Code must not search a list of strategies
  for a spelling and fall back to a placeholder, to another renderer, to
  `None`, or to dropping the fact.
- **Name a value where it is introduced.** A step that introduces a fresh
  value or memory state (a call result, a havoc, an allocation, a state
  between recorded points) gives it a name from its provenance at that
  point. Do not recover a name later from whatever locals happen to hold the
  value. A non-void call's result is `<region>.result`, including calls whose
  source discards the return value. The checked call transition retains the
  exact returned value, and its exit records it by region in
  `RecordedStates::call_results`. Lowering reads that value directly;
  integer and Boolean synthesis uses a reverse term index, and algebraic
  synthesis (a Rust enum a call returned) an index from the value to the
  first call that returned it (`algebraic_call_results`). Replacing or removing
  the recorded exit replaces or removes its result name too. A step's result
  is also named from the state that holds it (`ExecutionState::step_results`, by step
  number; `SourceExecutionLayout::step_region` maps the number to its step).
  A postfix update's result, the value it replaced, is
  `at(<its region>.entry, x)`.
  Source-layout result locals preserve allocation naming.
  A call that copies a by-value aggregate argument into its parameter object
  names that copy `<region>.parameter(name)`: the call producer hands back
  the memory just after the copies, with only those parameters bound
  (`kernel::CallParameters`), and the step records it as the region's
  parameter point (`ProgramPointKind::Parameters`). The callee's contract
  reads the copy there, so a step that prepares the call exposes that point at
  its pre-state while it proves the call's requirements, and the source-backed
  requirement spelling substitutes `R.parameter(name)` for the parameter.
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
  A loop head mints its pass count `K` fresh; the loop's phases spell it
  `iterations` (kernel placeholder `LOOP_ITERATIONS_VARIABLE`, bound per phase
  by `LoopIterationsScope`), and each path past the loop carries it on its
  correspondence metadata to the exit, which records it by loop in
  `RecordedStates::loop_iterations` with a reverse index from the variable:
  it is spelled `loop(i).iterations` in one lookup.
  Recorded points index each integer value, and each pointer's block, by the
  point and the local it was first given to (`RecordedStates::value_points`
  and `pointer_points`, filled from the locals each recorded state changed),
  and each symbolic integer or algebraic model-field value by the point whose
  resource instance first held it (`field_points`, filled from the instances each state changed), and
  each integer a memory cell came to hold by the point that recorded it there
  (`cell_points`, filled from the cells each memory changed). The structural
  speller writes `at(point, ...)` from these indexes for a value no nearer
  state names. A load or field read made in a memory no point
  records, inside a call or after the last point, is read at the nearest
  recorded memory that reads the same bytes.
  A local that keeps one value in memory, a borrowed Rust enum or
  type-parameter local (`AggregateLayout::holding_value`), is named by its
  own name: `o` lowers to the read of its object at the point it was last
  written (`ExecutionState::held_local_value`), never to a value a store left there,
  and that read spells `o`, or `at(point, o)` at the recorded point whose
  memory reads it.
- **Every fact kind has syntax.** A kernel fact that a proof state can hold
  has a Surface form. Adding a kernel fact or term form includes adding its
  Surface form and its spelling, in the same change.
- **A spelling lowers back to its fact.** The spelling of a fact, lowered in
  the same context, is that fact.
- **A refined goal keeps a spelling.** A step that refines a goal carries the
  goal's written spelling forward where it can, as `rewrite` rewrites it, and
  otherwise spells the new kernel goal (`Proof::spelled_goal`). Smart search
  also retains the refined goal's spelling: it reconstructs from source names,
  the current and entry states, and indexed recorded points, then checks the
  exact structural lowering. It does not run premise-spelling search or scan
  alternative local aliases for this presentation. A named goal remains an
  outstanding obligation; producing its spelling grants no proof authority.

A fact that exists only inside one kernel step, and never becomes a proof
state's fact or goal, needs no spelling.

## Shared term migration

`SurfaceTerm` is the source expression AST; `ContractExpression` remains a
compatibility alias. `KernelTerm` is an immutable typed expression DAG whose
arithmetic and call operands are themselves `KernelTerm`s. Its structural
identity is independent of equality-graph classes: constructing `1 + 1`
does not construct `2`. Nodes retain their result type, and checked arithmetic
constructors reject the wrong operand type or arity.

Specification-side Integer certificate arithmetic (`lower_surface_integer_term`)
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
See the live inventories in `roadmap/unspellable-facts.md`.
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
without reinterpreting it from the result's signedness. Widening spellings explicitly retain the source `int32`/`uint32`
interpretation: zero-extending signed `x` prints as `(x as uint32) as uint64`,
so lowering cannot replace zero extension with sign extension. Pointer-carrying
integers retain their complete metadata, even though their C type is numeric.
The six specialized 32/64-bit extensions and low-word conversions also use
shared cast nodes. A transitional encoding tag distinguishes their exact
legacy constructors from a generic cast with the same formats; import/export
never silently normalizes one into another. Low-word extraction interprets
its operand as unsigned bits, independent of the source C signedness.
Machine raising currently uses one exact export to the existing speller.
Integer bridge shortcuts are memoized per verification session (and reset when
restoring a reusable session), while the shared term identities remain stable.
Retaining a converted term across runs must not change a later run's deterministic
work count. Within a session, repeated conversions still reuse the cached bridge.

Mathematical observations of machine values (`to_integer`) now have a shared
`MachineObservation` node with the interpretation format and machine operand.
Signed and unsigned interpretations remain distinct. Raising retains the observation's interpretation inside any program point selector;
a local's name must not silently choose a different signedness. Narrow values retain their
existing load/conversion spelling: adding another narrowing or promotion cast
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
while its direct spelling lowered to the `Int64From32` spelling of `Cast`. Retaining the chain
restores the round trip. The existing 32-bit word-cast conventions remain.
The speller now handles explicit wide casts and wide literal payloads.
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

## Kernel authority

Some kernel propositions are checked context, not proof-state facts: a
resource composition (resources held together) and a predicate with no Click
name, such as subobject coverage or a volatile event. The kernel stores,
transports, and validates them with every other fact, so a step's delta still
justifies each one. No surface view presents or cites them: the census,
proof traces, diagnostics, and premise spelling all skip them, and a closing
step reads them from its context. One classification,
`Proposition::is_kernel_authority`, decides membership; code must not
special-case a composition or a `__click_` name elsewhere.

`held`, `same_object`, and contract facts are not authority even though the
kernel names them under `__click_`: `kernel::predicate_source_name` gives the
Click name that lowers to each, and the printer, synthesis, and authority
classification all read that one mapping.

The observed value carried by a volatile read event has a public spelling even
though the event predicate remains authority: `R.read_event(i).result`. Execution
records its exact typed value in the presentation state and indexes that value
for raising. Lowering retrieves it directly without consulting equalities or
performing another load. Internal handles therefore raise as event results,
not anonymous variables.

Making a proposition kind authority is a design decision, never a way to
avoid spelling a fact a proof could need to cite.

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
  spellings of one structure; the kernel need not produce every surface
  form. In particular `at(point, expression)` can raise at any program point
  whose recorded state selects the same version point for the read. Distinct
  program points may lower to the same read; raising picks one of them.
- Allowed: identifying two places whose values are structurally equal by a
  fact-free walk, which names one place twice rather than substituting a
  value. The version walk below is that case.
- Not allowed: substituting a known-equal term, constant-folding a
  comparison the facts decide, dropping a decided guard or disjunct, or
  choosing a term by known provenance. Equalities stay in the equality graph
  and the comparison form, which every check consults.

Logical object-pointer reads now retain their version names, including when
memory stores a complete pointer at the cell. The read's complete stored value
is related through `EqualityGraph::register_logical_read_values` and the
producer's read equations; its address, bounds, and designation are not folded
into the lowered term. The cached-prefix route also excludes logical reads
from fact-supported recovery, even outside specification scope.

Remaining violations include legacy stored-pointer folds outside this logical
read route (`complete_pointer_read_value` and `Pointer::loaded`), comparisons
folded to constants, decided guards and disjuncts dropped, and comparison kinds
chosen by known provenance. The logical-read switch does not establish complete
fact stability or spelling coverage.

## Lowering is fact-stable

Facts may decide whether lowering succeeds, discharge its obligations, and
add side facts beside its term. They never change the term: when a
proposition lowers both under facts and under no facts, the two terms are
the same up to the names of bound variables. A lowering that rewrites
through a fact, `f(a)` to `g(b)` because `f(a) == g(b)` is known, yields a
term that another context's lowering of the same text does not reach: `a ==
c` then no longer gives `f(a) == f(c)` by rewriting, and the fact holding
it has no spelling. Equalities belong to the equality graph, which every
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
wraparound. The speller structurally removes that implicit widening and writes
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
address equalities over a common exact wide stride retain full-width index
equalities. A table-read branch extends its context with its one new address
disequality before considering the next cell.

Boolean function applications, equalities, conditionals, and Boolean call
arguments spell structurally through their existing Surface syntax. Pure-theorem
premise spelling uses the retained typed source state and looks up names for the
selected fact's variables, rather than rebuilding an int32-only environment.
Generic calls spell the declared source name rather than the kernel's
`::<...>` instance suffix. Typed arguments (including explicit algebraic
constructors) reconstruct the same instance when lowered. Name selection must
include variables inside opaque call arguments and both goal binders and
proof-local witnesses, respecting `intro` shadowing.
Algebraic equality inside a Boolean expression spells as an ordinary comparison.
Match-arm algebraic bindings retain their source names for premise synthesis,
including list tails and C type-parameter values stored in constructors. These
names are selected from existing proof bindings; no equality search reconstructs
them.
A rewrite that introduces an outer Boolean negation retains lowering's truth
polarity: a false claim of `not p` is stored as a true claim of `p`. This does
not consult facts or change the Boolean term inside a larger expression.

Arithmetic domains spell as ordinary comparisons and conjunctions, including
the negation of a range conjunction on an overflowing execution branch.
`defined(expression)` denotes the full evaluation domain, including operand
domains. It does not stand for a single overflow component of division or shift.
`mdtests/arithmetic_definedness_is_one_ordinary_domain.md` checks the ordinary
bounds in both directions for signed 32/64-bit arithmetic.

Masked uint64 tag expressions retain their full numeric term. Exact tag-bound
lookups may produce a separate equality removing the masked tag; addition also
requires the word's low bits proved clear, so no carry reaches address bits.
Those facts accompany evaluation instead of replacing its result. Explicit
arithmetic certificates must conclude the full written goal (after explicit
rewrites), rather than depend on tag removal during lowering.

`CLICK_FACT_STABILITY=<path>` lowers each checked proof proposition again
under the same policy with no facts (`kernel::fact_stability`) and records
every lowering whose term differs. `scripts/fact-stability.sh` runs the
mdtest corpus under it and groups the differences by where the two terms
first diverge. The recent ordinary-corpus audits record zero differences;
[the handoff](https://github.com/clicklang/click/blob/master/roadmap/unspellable-facts.md) tracks their exact scope.
Historical defects included comparisons folded using facts, pointer and aliased
reads resolved through known values, comparison kinds chosen by provenance,
and decided guards dropped. Such equalities belong in checking, not in the
term lowering produces.

## A read names its version point

A Click read of an integer or object-pointer cell lowers to the read at the cell's version point,
never to the value a store left there: after `a[i] = 5`, `a[i]` lowers to the
read, not to `5` (`logical_read_names_its_version` in
`kernel::eval::memory_loads`). A read lowered to its stored value has no
spelling of its own: no Click text lowers back to it there, so `lower(raise(x))
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
`known()` after a store to an unrelated local.

A scalar read handle retains its structural descriptor (memory version,
address, and read kind) in the load registry. A generated read-definition fact
uses that same handle representation as source lowering; its producer binding
retains the exact registered descriptor. A reduced cache state must not
introduce a second raw-load form into the citable equation. Cache-only records
share the unchanged-bytes identity, while actual writes still create distinct
version points. Retaining typed read evidence checks the descriptor's epoch,
address and kind by indexed lookup, independently of the spelling.

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
  (`ProofFacts::with_fact`, `PureFactContext::assume_condition_once`), and an
  exact lookup also looks up the comparison form of what it looks up.
- A kernel rule that compares a stated term with one it derives compares
  their comparison forms (identity, cast identity, affine conclusions).
- `solve` tries a goal that reads stored cells over its stored values first
  (`try_stored_value_goal`), the search the goal had before reads kept their
  names, and searches over the reads only when that misses.

Code does not resolve reads anywhere else. A comparison form is a fact like
any other: a smart step that cites one spells it, and its spelling must lower
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
a separation premise): a name cannot depend on facts, each read is spelled at
its own point, and the frame fact relates them. A loop havoc is the same case:
the naming walk never crosses one, since the loop's checked footprint comes
from the proof's own annotation, so a read on either side keeps its own name
and the footprint relates them. The nightly audit lists the mdtests where the
load equality crosses such a footprint, and fails when one stops reporting. Two writes of one stored value
are two versions, related by the read-over-write authority.

## When a fact has no spelling

Report it as a tooling defect (the `inexpressible-fact` outcome in
[tracing](../concepts/tracing.md)), and fix it by naming the value at its
introduction or by adding the Surface form. Do not add a fallback, a
placeholder, a skipped candidate, or a declining route to work around it.

## Measuring the gap

`scripts/spellability-census.sh` runs the mdtest corpus with
`CLICK_SPELLABILITY_CENSUS` set (`src/surface/proof/spellability_census.rs`).
Each checked step records, for every fact it adds and for the goal it leaves
focused, whether the premise speller finds a checked spelling. The script
prints the misses grouped by kind. It separates steps a person wrote from
steps a smart tactic's search took: a search step needs a spelling only when
its search succeeds and is expanded, but a written step's facts and goal may
be cited by the next written step. The census only observes; it does not
change any proof. A unit test can record the same lines in memory with
`spellability_census::capture` and assert that a step's facts are spelled.

Audit-budget limitation (2026-10-31): enabling both census and fact-stability
instrumentation together pushes `solve_false_list_position_is_prompt` over
its 100,000-unit smart-work budget, changing the expected rejection diagnostic.
The ordinary gate and isolated runs with either flag pass that fixture. Run
the corpus audits separately for validation; do not increase the proof budget.
This is an instrumentation-accounting issue to investigate, not a recorded
fact-dependent lowering.

The census sorts a miss into one of three gaps, each with its own fix:

- **Writable but not found.** The fact has Click syntax and its operands
  have names, but the premise speller's search misses it: reflexive pointer
  equalities such as `p == p`, `viewable(p[0..1])` after an `unfold`, an
  applied theorem's conclusion such as `cd(n - 1) == 0`, and goals with no
  recorded presentation. The fix is the total speller.
- **A value with no name.** The fact mentions a value or address nothing
  names, printed `<unnamed A>` or `<pointer A>`: a callee's result, a havoc,
  an allocation. The fix is naming at introduction.
- **No syntax.** The fact's kind has no Surface form: writability, the
  memory a step may change.

The census does not count [kernel authority](#kernel-authority).
