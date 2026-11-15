# KernelTerm / SurfaceTerm: finish the representation split

Priority: P1.

Soundness: incomplete. No false acceptance is known from a missing spelling.
A missing spelling can lose proof completeness or prevent checked expansion.
Removing a compatibility checker without preserving its rules also loses
completeness and is not a valid migration.

## Goal and invariants

**Current priority: finish the KernelTerm / SurfaceTerm split.** This milestone
has a finite representation and consumer checklist. Eliminating every existing
spellability defect is a separate follow-up, not its completion criterion.

`SurfaceTerm` represents source expressions. `KernelTerm` is the common typed,
immutable expression DAG used by kernel expression producers and consumers.
Lowering can make implicit conversions explicit: two Surface expressions may
lower to the same kernel term. Raising a supported common term must preserve its
identity: `lower(raise(x)) == x`. The reverse direction preserves a canonical
spelling, not every detail of the original source text.

The broader requirement that every proof-state fact and goal has an exact
spelling remains in [Spellability](../docs/internals/spellability.md). Closing
this migration does not declare that broader project complete.

Preserve these rules throughout the migration:

- Lowering is structural and fact-stable. Facts may discharge obligations or
  establish equalities; they must not choose or simplify the constructed term.
  Equalities belong in the equality graph or comparison form.
- Definedness remains separately scoped ordinary propositions, discharged by
  ordinary proof checking. Preserve the current C/Rust and specification
  semantics; this migration does not redesign them or restore guards in values.
- Preserve positive proofs, refusals, unknown answers, source evidence and
  branch isolation. Replacing a compatibility rule by an unknown answer is not
  migration completion.
- Work stays near linear up to indexing factors. Do not export a growing DAG to
  a boxed tree at every prefix, repeatedly index all its variables, or scan
  ambient facts/history to recover a representation.
- Values and effect points retain their introducing names: call `.result`,
  heap `.allocation`, recorded states and volatile `.read_event(i).result`.
  Internal handles are permitted; they are not public spellings.

## Current position

Historical starting baseline: `1dcc52be1`, including merged PR #2581.
The delivery table below records the current migration status.

Already landed:

- Common `KernelTerm` nodes and `SurfaceTerm`; `ContractExpression` is an alias
  of `SurfaceTerm`, not a separate expression tree.
- Shared machine arithmetic, casts and many comparison, interval, certificate,
  rewrite and dependency consumers. Ordinary definedness obligations are
  separate from lowered terms.
- Structural ordinary integer, object-pointer and function-pointer reads,
  including historical read identities and shared address-index operands.
- Volatile observation result names (#2492), with typed value retention and
  branch/indexing controls. Specification reads no longer emit C access events.

**The split is not complete.** Common roots are live for supported numeric
evaluation, calls, execution handoffs, range folds, numeric/algebraic match
results, and complete pointers/read addresses. Chunk 7 covers pointer formation,
arithmetic, calls, branches, locals, returns, temporary statement results and
memory storage/receipt. Remaining packages are Boolean and opaque result
families (8), the general raise/lower and certificate boundary (9), and duplicate
storage removal/final closure (10). Named native checking, ABI, nonpointer-cell
and presentation compatibility consumers remain explicit; closing chunk 7 does
not close those packages. These are
representation boundaries, not a count of every remaining verifier defect.

The previous document interleaved open boxes with later paragraphs completing
parts of them. Its old unchecked lists and historical accessor counts must not
be treated as a current to-do list. The detailed evidence is preserved in
[the pre-revision roadmap](https://github.com/clicklang/click/blob/93c5fe74cd6ff161782b65a9709ffe57cd3eca76/roadmap/unspellable-facts.md).

## Authorized delivery sequence

The next ten work packages each receive at least one PR. A package is closed
only when its named boundaries and regression coverage are complete; these are
not ten aliases for partial progress on one boundary. Keep one PR open at a time.

| Chunk | Work package | State |
| --- | --- | --- |
| 1 | Let bindings and local value handoffs | Merged in [PR #2617](https://github.com/clicklang/click/pull/2617); specification bindings retain shared values through selected lookups, with shadowing and state scope preserved. |
| 2 | Symbolic conditional joins | Merged [PR #2638](https://github.com/clicklang/click/pull/2638). Typed guards and shared arms survive checking, transport, state matching and Surface spelling. The full gate passed 7,294 unit/API tests, 5,240 fixtures and all examples; its 15m54s run exceeded the ten-minute target. The final conditional-equality follow-up passed 1,884 selected checks, including all scaling, Rust import and expansion tests. Its full-corpus fact-stability audit passed all 5,240 fixtures with zero differences. |
| 3 | Pure-function arguments and results | In progress. [PR #2643](https://github.com/clicklang/click/pull/2643) retained shared machine values during argument assembly. [PR #2647](https://github.com/clicklang/click/pull/2647) retains them in call payloads and migrates argument collection, rewriting, alpha keys, congruence and fold-read consumers. Typed semantic application identity is separate from exact producer payloads; numeric indexes share native/retained call identities, and comparison cycle guards permit narrow-to-wide checking. Repeated native/shared readings do not accumulate payload versions. The integer machine call-result sequence 3a–3f below completes common result production and its consumers; pointer, algebraic, Boolean and floating-point result families remain separate work. |
| 4 | Mixed-width arithmetic and casts | Implemented as subchunks 4a–4j below, one PR per subchunk. Numeric producers retain shared operands and results within the existing supported profile. General call and nonnumeric compatibility boundaries belong to the remaining packages; the previous combined branch stays unmerged reference material. |
| 5 | C/Rust execution result carriers | Supported machine handoffs implemented in 5a–5g below: expression paths, local bindings, returns and caller receipt retain common roots. Native memory-cell, specification and presentation boundaries remain explicit. |
| 6 | Folds, binders and algebraic matches | Implemented as 6a–6n below. Common fold and numeric/algebraic match results retain scoped children; remaining native consumers are named compatibility boundaries. |
| 7 | Complete pointers and read addresses | Implemented as 7a–7u below, one PR per slice. Supported pointer producers and execution/storage handoffs retain common roots; checking and Surface consumers preserve metadata, state identity and existing rules. |
| 8 | Remaining Boolean and opaque expression payloads | Inventory and authorized PR sequence below; implementation open. |
| 9 | Unified raising/lowering and certificate boundaries | Open |
| 10 | Duplicate storage removal and final closure | Open |

## Chunk 3: machine-valued pure-function results

Finish the remaining machine-valued call-result boundaries in six sequential
PRs, preparing consumers before switching the evaluator. Pointer, algebraic, Boolean and
floating-point result families remain in their own packages. Preserve existing call
semantics, exact producer metadata, proof/refusal behavior and fact stability;
do not introduce search strategies, indexes or larger budgets to compensate for
representation changes.

| Subchunk | Boundary | Completion criterion |
| --- | --- | --- |
| 3a | Common result roots | Typed common calls preserve the function, ordered arguments, result type and exact opaque producer payloads; native/shared numeric inputs agree. |
| 3b | Numeric consumers | Observations, casts and arithmetic retain common machine call operands without prefix exports. |
| 3c | Comparison and fact matching | Existing comparison/equality keys preserve native/shared rules, source premises and refusals. |
| 3d | Rewriting and transport | Substitution, rewriting, dependencies and state handling retain common call roots and their arguments. |
| 3e | Surface boundary | Calls round-trip through raising, lowering and certificate paths with exact term identity. |
| 3f | Producer switch and closure | Actual call evaluation returns common machine roots; nested calls and result handoffs retain them, and obsolete adapters for this boundary are removed. |

3a adds the explicit common-root constructor and machine export route without
switching the evaluator or admitting calls into the shared machine operand
fragment. Opaque argument descriptors use the retained application's exact
payload identity, separately from semantic application equality. Consumers are
prepared in the following slices before producer activation.
[PR #2686](https://github.com/clicklang/click/pull/2686) merged and its pushed
commit was verified on upstream. All 1,536 selected tests (including all 1,525
scaling tests) and all 5,275 regular fixtures passed, with zero fact-stability
differences.

3b admits common integer call roots to numeric operand views, preserving their
root in mathematical observations and retaining argument handles in the cached
compatibility reading. Casts and arithmetic retain their operands and ordinary
definedness debts. The native 128-bit call-root refusal includes identity casts;
the shared shortcut reports the same type error without exporting arguments.
[PR #2690](https://github.com/clicklang/click/pull/2690) merged and its pushed
commit was verified on upstream.

3c gives common call observations the existing native typed application key,
without replacing their exact producer roots. Comparison sources retain their
written premises, polarity and branch authority. The existing observation memo
walks selected children once; repeated queries do not scan accumulated facts.
[PR #2691](https://github.com/clicklang/click/pull/2691) merged and both pushed
commits were verified on upstream. It also admits common calls to the existing
typed congruence registration. The final fixture audit passed with zero differences.

3d retains common call roots through checked substitutions, exact rewrites and
pointer-index transport. Unchanged leaves keep exact payload identity; changed
calls rebuild common arguments. Native/shared selected-source matching uses the
existing typed application identity. Pure-call arguments retain their original
states under transport, following the native rule. No new search or index is
introduced. [PR #2694](https://github.com/clicklang/click/pull/2694) merged and its
pushed commit was verified on upstream. All 1,699 selected regressions and all
5,275 regular fixtures passed, with zero fact-stability differences.

3e imports native integer calls through the common call constructor and retains
nested numeric argument structure at the Surface boundary. Raising an ordinary
machine call spells its selected integer type explicitly, including a signed
reading of an unsigned call. Native 128-bit call identity-cast refusals remain
unchanged. Source roundtrips cover all ten integer result types, nested calls,
casts and arithmetic; certificate checks preserve definedness and selected
premises. [PR #2697](https://github.com/clicklang/click/pull/2697) merged and
its pushed commit was verified on upstream. All 1,642 selected regressions and
all 5,275 regular fixtures passed with zero fact-stability differences.

3f switches the actual integer pure-call evaluator to common result roots for
all ten integer formats. Nested calls and deferred bindings retain their
arguments; native result handoffs use the existing root reading with shared
numeric argument handles, instead of structurally exporting the argument DAG.
Explicit structural export remains available at its named boundary. Projection
of an existing constructor field still returns that field, and other result
families retain their existing producers. The native producer remains as the
parity-test control and the fallback for unmigrated result sorts. Tests cover
actual production, native parity for arithmetic and definedness, wide cast
refusals, selected fact identity and linear nested-call handoffs with zero
machine exports. Pointer-dependency discovery in the equality graph reads
common calls through the existing call-argument path, retaining complete-pointer
equality requirements. Direct call comparisons preserve their native machine
fact form instead of selecting Integer rewrite/search dispatch merely because
the producer is shared. MemoryState keys reinterpret conditional operands at their
existing canonical observation type for every integer format. Native comparison
and algebraic reflexivity readers use the existing typed application identity.
The existing rewrite history uses state-aware proposition identity so fresh
argument carriers do not restart visited branches; search strategies and limits
are unchanged. Calls whose numeric arguments are already retained borrow their
producer's application payload for compatibility reads. Boxed numeric inputs
still import to shared children, including when an equivalent shared producer
later reuses their root. Scaling checks cover borrowed readings, nested handoffs,
and rewrite identities that distinguish states, formats and polarity.
Certification compares retained arguments by written call syntax, including
algebraic variables, applications and exact state reads, without replacing
that syntax comparison with arithmetic observation equality.
[PR #2701](https://github.com/clicklang/click/pull/2701) closes the integer
call-result sequence, not the wider KernelTerm/SurfaceTerm migration or the
other result families.

## Chunk 8: remaining Boolean and opaque expression payloads

Deliver sequentially, one PR per row. Prepare consumer support and existing
Surface spelling before switching live producers. Preserve exact producer
metadata separately from observation/fact identity, existing reductions and
refusals, binder scope, states and evidence. Do not add search, indexes or
larger budgets. General raising/lowering and certificate consolidation stays in
package 9; duplicate-storage removal and final migration closure stay in 10.
Routine sequencing changes are allowed; discuss unexpected semantic or scope
changes before implementing them.

| Subchunk | Boundary | Completion criterion |
| --- | --- | --- |
| 8a | Payload inventory | Assign live legacy expression paths and distinguish opaque identities from expression trees. |
| 8b | Boolean operand views | Inspect common Boolean roots without exporting entire conditions. |
| 8c | Boolean dependencies | Variables, captures and memory dependencies follow common children. |
| 8d | Boolean substitution | Preserve shared children and binder scope. |
| 8e | Boolean state transport | Preserve read identities and evidence requirements. |
| 8f | Boolean identity and fact keys | Preserve native/common matching and comparison-format equivalences. |
| 8g | Pointer-offset equality | Retain shared offset operands. |
| 8h | Raw pointer equality | Retain shared address operands. |
| 8i | Complete-pointer equality | Preserve designation, extent and complete-payload distinctions. |
| 8j | Overflow conditions | Retain typed operands and existing operation/width rules. |
| 8k | Boolean reads | Retain state and shared address. |
| 8l | Boolean pure calls | Retain common arguments and result structure. |
| 8m | Boolean composition and casts | Equality, conditionals and Boolean-to-machine conversions preserve children through production. |
| 8n | Boolean local/call handoffs | Bindings, arguments and returns retain roots. |
| 8o | Boolean storage and temporary results | Memory receipt and statement-result handoffs retain structure. |
| 8p | Algebraic atoms and constructors | Typed variables and constructor fields replace generic wrappers. |
| 8q | Algebraic projections and variant tests | Use common operands with existing reductions/refusals. |
| 8r | Algebraic equality | Preserve constructor and type distinctions. |
| 8s | Algebraic pure calls | Retain common arguments and results. |
| 8s.1 | Algebraic conditionals | Retain condition and both branches with existing reduction behavior. |
| 8s.2 | Algebraic reads | Retain memory state, address and abstract type. |
| 8t | Algebraic handoffs | Bindings, result carriers and package-6 matches preserve roots. |
| 8u | Float value foundation | Typed literals/views preserve exact bits, widths and identity. |
| 8v | Float reads | Retain common addresses and exact states. |
| 8w | Float arithmetic | Existing negation and binary operations retain operands. |
| 8x | Float conversions | Existing integer/float and width conversions preserve definedness. |
| 8y | Float conditions | Comparisons/classifications preserve NaN and signed-zero behavior. |
| 8z | Float pure calls | Retain common arguments and results. |
| 8aa | Float execution handoffs | Locals, arguments, returns and temporary results retain roots. |
| 8ab | Float memory storage | Store/load retain structure through the existing memory model. |
| 8ac | Mixed-family argument adapters | Migrated Boolean/algebraic/float/pointer/numeric expressions no longer receive generic wrappers in calls. |
| 8ad | Closure | Remove superseded adapters; validate nested combinations, Surface round trips, fact stability and scaling; account for every remaining legacy arm. |

8a records the baseline inventory and authorized sequence in merged
[PR #2801](https://github.com/clicklang/click/pull/2801). The docs-only gate
passed all 44 documentation tests.

8b (merged [PR #2805](https://github.com/clicklang/click/pull/2805)) adds borrowed Boolean operands and a borrowed machine-conditional view.
Shape and branch-only readers in decision dispatch, interval checks, state
keys, syntax ordering and equality-graph admission no longer export the guard.
Consumers that actually require native conditions keep an explicitly named
compatibility conversion. This prepares the following dependency and rewrite
slices without switching producers or changing proof rules. Native/shared view
regressions preserve written comparison formats and exact opaque payloads; a
multi-size regression checks that inspecting growing guards does no export work
beside unrelated arena terms. All 1,753 selected tests passed, including every
scaling test and the Boolean, condition-reasoning, state-key and equality-graph
selections.

8c (merged [PR #2806](https://github.com/clicklang/click/pull/2806)) gives standalone Boolean roots the existing five scoped variable-reader
modes and walks shared Boolean connectives once for resource-read and state
dependencies. Comparison operands use the existing shared machine readers;
Boolean calls stay opaque to these memory readers. Resource operand stacks
preserve the native reader's first-occurrence order. Selected Integer-comparison
leaves still use the existing native structural classifier, preserving its
restricted admission rather than broadening memory discovery. This is an
explicit selected-leaf compatibility boundary, not an export of the surrounding
Boolean DAG. All 1,693 selected tests passed, including all scaling tests,
resource tracking and variable collection. New regressions pin mode agreement,
read/state order, opaque-call behavior and shared-connective traversal work.
After integrating upstream through `7a681179b` (including #2802 and #2804),
all 1,729 integration selections passed, including every scaling test and the
contract-claim tests.

8f (merged [PR #2808](https://github.com/clicklang/click/pull/2808)) prepares identity and fact-key consumers before completing 8d/8e. Primitive
Boolean comparison matching reads retained machine operands through the existing
comparison-format identity. Exact Boolean identity walks common connectives
once and preserves native comparison-format equivalences; numeric call arguments
remain typed handles for application identity. Composite guards retain their
exact-equality-only load policy. MemoryState keys inspect guard shape without
exporting it and key eligible primitive comparisons through shared operands;
Integer comparisons and Boolean value forms keep their existing exact enclosing
operand keys. Selected Integer comparison atoms retain the existing structural
classifier, and opaque leaves retain their native family identity. Explicit
native syntax ordering remains a compatibility boundary.

Validation: 1,635 selected tests passed, including every scaling test, Boolean
view/identity tests, state operand keys and shared load-atom comparisons.
Regressions cover native/shared format agreement, composite load-authority
refusal, linear shared-connective identity and growing arithmetic comparison
prefixes without machine exports. No proof rules, search indexes or budgets
changed. The following 8d/8e slices reuse this identity support.

8d (merged [PR #2810](https://github.com/clicklang/click/pull/2810)) prepares common Boolean bitvector/pointer substitution for the producer and
handoff slices. Bitvector substitution preserves raw Boolean connectives and
uses the existing shared arithmetic normalization mapper; one local memo shares
numeric work across comparison atoms. Pointer substitution preserves its distinct
native Boolean folding policy, scoped carrier reservation and read states.
Comparison reconstruction preserves written formats, width-specific reductions,
address/zero and alignment rules. In particular, unsigned 32-bit equality keeps
its written format, and bitvector substitution keeps signed 64-bit equality raw.
Typed call arguments retain shared machine operands through their existing
substitution route; selected Integer and opaque atoms keep their native family
routines. Refused common operand rewrites propagate failure. General native
proposition/certificate boundaries remain in package 9; producer activation stays
in the later Boolean slices.

Validation covers native/common constructor and substitution parity across all
integer widths, address and mask rules, fold capture, pointer connective folding,
read states, and shared connective/overlapping arithmetic-prefix scaling.
All 1,741 selected tests passed, including every scaling test and the substitution
selections, with pinned importer tools. The CI-quality check passed.

8e (merged [PR #2811](https://github.com/clicklang/click/pull/2811)) connects shared pointer-index transport to a common Boolean guard boundary.
Common constants, variables, connectives and calls retain the existing refusal
without exporting the guard DAG; Boolean loads retain their native refusal.
Primitive comparisons transport shared operands through the existing frame
reader and the shared equivalent of native comparison constructors. Unchanged
guards retain their original roots through native-equivalent Boolean identity.
Selected Integer and opaque condition families keep their existing compatibility
readers. Other index mappers keep their explicit native guard adapter; the
numeric Boolean-cast compatibility boundary remains assigned to 8m.
Native/common transport agreement, states, comparison-constructor behavior,
constant-work refusal and accepted shared arithmetic transport without exports
are covered. The shared Boolean matcher also restores the native exact-equality
precedence before load authority: an identical guard, including comparison-format
equivalences, does not need permission to match its own read. That preliminary
check reuses the existing immutable machine syntax memo. All 1,679 selected tests
passed, including every scaling test, memory provenance and shared load-atom
comparison selections, with exit status 0. The CI-quality check passed.

8g (merged [PR #2813](https://github.com/clicklang/click/pull/2813)) replaces the whole-condition pointer-offset equality fallback with a typed
pair of shared offsets. Imports and explicit exports preserve the written Add
shape, scales, index carrier types and signedness. Boolean identity, load-atom
matching, variable/capture/binder readers, memory/resource dependencies and
state selectors read the retained operands directly. Native exact equality
still precedes load authority; only the existing narrow-index path admits
load-atom matching, while wide indices retain exact identity.

Substitution preserves unchanged offset spelling and each existing raw/smart
reconstruction policy. Frame transport reuses the package-7 pointer transporter
with one context for both operands. Its offset-add implementation is shared with
substitution; immutable constant metadata avoids rescanning prefixes. The
existing residue classifier keeps its 64-occurrence, stride and constant limits.
Numeric observation normalization retains its producer/observation distinction
and shares offset-prefix work. No search, authority or budget rules change.
The explicit Surface output boundary still uses the existing address-context
offset spelling; the general raise/lower boundary remains package 9.

The initial broad selection passed all 1,673 tests, including every scaling test,
constructor/substitution/transport parity, annotation identity, dependency widths,
state keys and doubled/growing offset DAGs without numeric exports. Integration
validation against the subsequent pointer-read/state-control changes is recorded
with the PR. Boolean execution handoffs and the other package-8 families remain open.

8h (merged [PR #2816](https://github.com/clicklang/click/pull/2816)) retains raw pointer equality as a typed pair of shared addresses. Block
identity, shared displacement, exact producer metadata and semantic observation
identity remain separate. Dependency readers preserve native admission and
ordering, including loaded-pointer defining reads and right-first resource
displacement traversal. MemoryState selectors and load matching reuse the existing
shared-address readers; narrow and wide indices retain their existing authority
rules. Frame transport uses one context for both addresses.

Substitution preserves the distinct native rules for top-level pointer conditions,
nested Boolean values and pure-call pointer blocks. Numeric indices keep their
existing raw or smart reconstruction policy, and replacement offsets retain their
written structure. Opaque block rewriting stays at its existing compatibility
boundary; no search, budgets or pointer semantics change. Explicit Surface output
continues through the existing address-context adapter. Complete-pointer equality
is the separate 8i slice.

Validation: all 1,716 selected tests passed, including every scaling test,
raw-pointer constructor/substitution parity, block and state identity,
load authority, read ordering, dependency modes and frame transport. The
CI-quality check passed.

8i (merged [PR #2818](https://github.com/clicklang/click/pull/2818)) retains complete-pointer equality operands, including designation, opaque
extent, explicit extent and exact qualifiers/evidence. Its observation identity
uses the native logical fields without changing the producer payload. MemoryState
selectors and dependency readers use shared address roles directly; extent widths
retain each reader's existing admission policy. Load matching still accepts exact
identity only. Framed condition transport reuses the existing complete-pointer
transporter, preserving its reconstructed-word designation policy.

Bitvector substitution maps addresses while preserving extent widths. Formal
pointer substitution keeps the native complete-value designation and opaque-domain
replacement rules, followed by the existing address canonicalization and equality
constructor reductions. Surface output keeps its explicit compatibility adapter.

Validation: all 1,723 selected tests passed on current upstream, including every
scaling test, native constructor/substitution/transport parity, complete-domain
state keys, dependency admission, read order and observation identity. Exact
producer metadata stays retained while logical keys preserve the native const,
volatile, type and extent distinctions. The CI-quality check passed.

8j (merged [PR #2821](https://github.com/clicklang/click/pull/2821)) retains overflow conditions as typed numeric operand pairs with their exact
format and operation. Identity, observation normalization, state selectors,
dependency readers and load matching inspect the shared operands directly.
Reconstruction reuses the existing constant and width-interval rules. Bitvector
substitution and frame transport use smart construction; top-level pointer
substitution preserves the condition, while nested Boolean pointer substitution
rebuilds it raw. Explicit Surface output keeps its compatibility adapter.

Validation: all 1,727 selected tests passed, including every scaling test, all
machine formats and overflow operations, constructor and substitution parity,
load authority, exact format/operation keys, dependencies and frame transport.
Shared arithmetic DAGs remain retained without numeric exports. The CI-quality
check passed.

8k (merged [PR #2822](https://github.com/clicklang/click/pull/2822)) retains Boolean reads as typed state/shared-address nodes. Producer keys
keep exact state arenas and address spelling; observation identity preserves
native memory and address equality. Substitution retains the existing state
and raw/smart address policies. Variable, capture, binder and memory-dependency
readers preserve their distinct admission rules and read order. Resource
diagnostics still report only the one-byte Boolean cell; their selected native
read descriptor is cached without exporting an enclosing Boolean expression.
Frame transport and load matching retain the existing Boolean-value refusals.
Surface output remains at its explicit compatibility boundary.

Validation: all 1,907 selected tests passed on current upstream, including every
scaling test, Boolean-read substitution and identity parity, dependency widths
and ordering, resource diagnostics and the intervening MIR temporary tests.
The CI-quality check passed.

8l (merged [PR #2824](https://github.com/clicklang/click/pull/2824)) produces Boolean pure-call results as common Bool roots. Numeric arguments
remain shared, and opaque argument descriptors retain exact producer identities.
A cached selected call reading preserves shared numeric arguments at native
handoffs. Observation normalization uses native semantic argument identity while
producer roots retain differing pointer annotations. Execution result type and
native output support the retained call; the separately scheduled local/call,
storage and mixed-family argument slices still own those remaining boundaries.

Validation: all 1,869 selected tests passed on the integrated upstream tree,
including every scaling test, contract completion, Boolean call result production and native handoff parity, exact descriptor and
semantic observation identity, shared call argument rewrites, Boolean spelling,
and existing numeric/pointer call producers. The CI-quality check passed.

8m (merged [PR #2828](https://github.com/clicklang/click/pull/2828)) retains Boolean composition and casts through production. Conditional and
equality constructors preserve the native root reductions; Boolean-to-machine
casts retain their logical operand and written destination. Raw C Bool words
still enter through their existing nonzero test, and comparisons with integers
or ordering operations keep their refusals. Equality's proposition output remains
an explicit native boundary.

Retained casts participate in the existing conversion readers, graph registration,
dependency and rewrite policies, and semantic observation normalization. Pointer
discovery keeps native cast opacity, and exact source matching keeps native
argument equality. Reading a retained
local cast emits its original certified range facts through the selected native
cast descriptor. General output spelling and later local/storage handoffs retain
their assigned slices; no search or budget policy changes.

Validation: all 2,410 integration tests passed, including every scaling test,
C frontend and fact-reasoning selections,
constructor reductions, all integer cast formats, producer parity, observation
identity, local range-fact preservation, equality rewrites, dependencies and the
modeled-binary-tree example. The C/C++/Rust integer-language examples and focused
cast-dispatch regressions passed separately. The CI-quality check passed.

8o (merged [PR #2832](https://github.com/clicklang/click/pull/2832)) retains Boolean roots in local/outcome storage, memory cells and statement
results, preceding 8n because its local/call handoffs need this storage support.
Storage identity still uses the original native equality, hash and order rules,
including comparisons with other value families. The selected Boolean native
view reuses the existing argument cache; raw C Boolean words remain exact native
values. Ordinary pointer queries do not materialize Boolean compatibility views.

Same-type Boolean assignments, temporary-result handoffs and memory receipts
preserve the producer root. A byte write that assembles a wider integer keeps
that integer result, and changed-type conversions keep their existing behavior.
General native output and replacement of compatibility keys remain later work.
Validation: all 1,898 integration tests passed, including every scaling test,
preservation proofs and memory provenance,
Boolean storage key agreement, actual statement stores and memory reloads,
temporary result receipts, byte-view cases and existing pointer handoffs.
Growing-prefix storage and retrieval perform no operand traversal or numeric
export. The ordinary example projects and CI-quality check passed.

8n (merged [PR #2834](https://github.com/clicklang/click/pull/2834)) retains logical Boolean arguments through specification call assembly and
nested Boolean call production. Native argument compatibility borrows the
selected cached descriptor. Lexical bindings keep their common roots, and
same-type runtime parameter binding, return conversion, contract-result binding
and caller result assignment preserve those roots. Raw C Boolean words and
changed-type conversions keep their original behavior; no refusal or authority
rule changes. Numeric-result mixed-family call adapters remain assigned to 8ac.

Regressions cover nested call/let argument identity and native output agreement,
runtime argument and return handoffs, raw-word preservation, and nested-call
scaling without numeric exports. Dependency-reader agreement covers Boolean
arguments containing Integer comparisons and memory reads in every collection
mode, with call-connection collection enabled and disabled. All 1,994 integration
tests passed, including every scaling test, termination and contract completion,
Integer conversion checks and ordinary example projects.
The CI-quality check passed.

8p ([#2835](https://github.com/clicklang/click/pull/2835), merged) represents
algebraic variables and constructors directly in common roots,
reusing the prepared constructor payload. Imports retain typed Integer/numeric
and nested algebraic fields; unmigrated field families retain exact native
payloads rather than coalescing pointer annotations through value equality.
Iterative import and explicit export visit source/output nodes once instead of
copying every boxed prefix.

Constructor observation keys normalize their shared fields through the existing
native observation rules. Producer roots retain exact metadata. Variable readers
preserve the distinction between free Integer variables in a match scrutinee and
Integer carriers, including declarations, in ordinary algebraic arguments.
The existing algebraic Surface spelling handles these roots at the explicit
output boundary. Selected constructor source comparison remains a native
compatibility boundary for the algebraic-equality slice; calls, conditionals,
reads and execution handoffs retain their separately assigned slices.

Validation: 2,128 selected tests passed, including every scaling test, algebraic
and retained-match readers/rewrites, Surface synthesis, Rust lowering and the
full ordinary example projects. `scripts/check.sh --ci-quality` exited 0.

8q ([#2836](https://github.com/clicklang/click/pull/2836), merged) selects common
constructor variants directly during retained-match reduction.
The existing schema/type refusals and typed field-replacement policy are retained;
only the selected fields cross that remaining substitution adapter. Symbolic
common roots decline reduction without materializing algebraic output.

Pure-function projection now accepts common constructor arguments and returns the
selected field root without exporting siblings or arithmetic prefixes. Native
inputs retain their existing projection behavior. Algebraic call-argument and
runtime enum-carrier activation remain with their assigned call/handoff slices.
Focused regressions check variant/index/type refusals, exact pointer payloads,
native/common field-checking parity, and constant selected-field projection work.
Validation: five focused tests and 2,040 broader tests passed, including all
scaling tests, algebraic/match checks, Surface synthesis, Rust lowering and full
ordinary example projects. `scripts/check.sh --ci-quality` exited 0.

8r ([#2837](https://github.com/clicklang/click/pull/2837), merged) retains both
algebraic equality operands in a typed common condition node.
Constructor/variable syntax comparisons traverse shared fields and match children,
with native field equality preserving type, variant, order and pointer-metadata
semantics. Exact producer payloads remain distinct. Constructor source matching
uses this comparison instead of exporting the whole common constructor.

Observation-key normalization follows the retained operands, and dependency
readers preserve the native carrier/binder policies. Existing Surface equality
spelling and native condition consumers use explicit output adapters. Scoped
native field substitutions, call/handoff activation and the general raise/lower
boundary remain assigned to their existing slices. No equality search rules or
budgets changed. Regressions cover exact payloads, old/new views, operand order,
native/common observation keys, readers and linear shared-constructor comparison.
Validation: 2,010 selected tests passed before integration. After incorporating
upstream call/destination-write retirement, 3,045 tests passed, including every
scaling test, algebraic/Boolean checks, rewrites/readers, Surface synthesis, call
and statement checks, language lowering and full ordinary example projects.
`scripts/check.sh --ci-quality` exited 0 on the integrated tree.

8s ([#2838](https://github.com/clicklang/click/pull/2838), merged) retains
algebraic pure-call arguments and results as common roots, preserving
native `Value(machine)` versus `SharedMachine` argument forms. Explicit output
reconstructs those forms and exact pointer metadata. Syntax comparison, dependency
readers, observation normalization and existing Surface call spelling understand
the retained call. Mixed-family descriptor adapters remain assigned to 8ac.

Native algebraic matches now import iteratively so retained match arguments have
the same observation keys as native inputs. Normalization follows opaque fields
through algebraic matches while preserving their result type. Recursive call
evaluation uses smaller helper frames with unchanged expression-step accounting,
path facts and obligations, including `to_nat` definedness. No search or resource
limits changed. Five focused regressions passed, covering exact argument forms,
retained-match keys, reader modes and linear nested-call/match-import work.
Validation: the broader run passed 2,788 tests, including all other scaling
checks and full ordinary examples. Its sole failure was a fixture assuming a
zero-argument algebraic call remained opaque; after giving it an opaque pointer
argument, that regression and the five focused checks all passed. The quality
gate exited 0. No production behavior or test limits changed for that adjustment.

8s.1 ([#2839](https://github.com/clicklang/click/pull/2839), merged) retains
algebraic conditional guards and both branches. Import/export
preserves written conditional structure, while production keeps the existing
literal-condition and equal-arm reductions without exporting branch trees.
Syntax equality, observation normalization, dependency readers and existing
Surface `if` spelling follow the common children. No fact-dependent lowering,
obligation rule, refusal or resource limit changed. A small Surface helper keeps
the general recursive dispatch frame within the existing stack limit.

Conditional parity testing also caught and corrected an 8s argument-identity
regression: re-creating a SharedMachine carrier from its imported root can change
its native identity. Calls now preserve that immutable handle for explicit output
and compare it by its existing ID, while retaining the common child separately.
Observation carriers and exact producer carriers keep their distinct equality
policies. Thirteen focused tests passed, including this reproduction, raw/reduced
native parity, opaque observation keys, readers, nested import/export and actual
evaluator scaling, and the existing deep-synthesis budget regression.
Validation: all 2,794 selected tests passed, including every scaling test,
algebraic/Boolean/call/nat checks, readers/rewrites, Surface synthesis and full
ordinary example projects. The quality gate exited 0.

8s.2 (merged [PR #2840](https://github.com/clicklang/click/pull/2840)) represents algebraic reads with their abstract type, exact state and
shared address. Boolean and algebraic reads reuse the same state descriptor,
keeping producer arena identity separate from native observation equality.
Import/export, syntax comparison, observation normalization and existing Surface
read spelling support the common form. Selected algebraic read results retain
it; broader binding and execution handoffs remain 8t.

Dependency readers preserve the native UInt64 read-carrier policy, including
stored-load connections and havoc origins. Read resolution, canonical state
selection and evidence requirements remain unchanged. Fourteen focused tests
passed, covering state/type identity, native/common keys, all reader modes,
actual read results, constant-work construction with growing shared addresses,
and existing Boolean read and algebraic fact-key regressions.
Validation: all 2,214 broader tests passed, including every scaling test,
abstract/parameter/memory checks, algebraic and Boolean behavior, readers,
rewrites, Surface synthesis and full ordinary example projects. The quality
gate exited 0.

8t ([PR #2841](https://github.com/clicklang/click/pull/2841)) retains algebraic roots through specification bindings, constructors and
selected match fields, algebraic-valued program matches, execution locals,
arguments, returns, assignments, temporary results and memory cells. Runtime
enum construction and field selection use common fields directly. Native key
adapters preserve the existing equality, ordering and hash contracts. A named
algebraic leaf has a direct compatibility reading without an export walk.

Program-carried parameter arguments and fields retain their distinct native
argument form at the mixed-family adapter (8ac). Native Integer result readings,
required-construction records, fact-witness lookup and public native output
remain explicit compatibility boundaries; this slice does not redesign their
contracts. Ordinary program conditionals still refuse unequal algebraic arms;
logical algebraic conditionals retain the separate 8s.1 behavior. No search,
evidence, budget or language changes are included.

Thirty focused tests passed, including nested constructor binding/selection,
runtime field refusals, storage key parity, conditional refusal parity and
constant-work construction around growing shared fields. All 2,540 broader tests
passed, including argument/return/caller-result retention, program-call result
parity, every scaling test and the full ordinary example corpus. The quality
gate exited 0.

Before 8u, the approved float-spelling prerequisite ([PR #2844](https://github.com/clicklang/click/pull/2844)) adds literal-only
`float32_from_bits` and `float64_from_bits` forms. These preserve exact IEEE
bits and the existing native carrier identity across printing and parsing,
including signed zero and NaN payloads. They add no arithmetic or proof rules.
The common float representation remains the separate 8u slice. The 241-test
parser, Surface, diagnostic and documentation selection passed, as did the
final 75-test float/documentation selection including the float proof fixtures.
Fact-stability instrumentation reported zero changed lowerings.

8u imports Float32/Float64 constants and variables as typed common atoms.
Literal nodes keep the exact native carrier and bits; borrowed views expose
width, literal and variable shape without exporting a prefix. Native export
and Surface raising preserve signed zero, NaN payloads and carrier identity.
The five variable-reader policies remain unchanged. Compound float operations
remain explicit native boundaries for 8v–8z, and execution/storage activation
remains 8aa–8ab. The mixed argument adapter retains native float descriptors
until 8ac. Six focused float tests passed. The broader 1,936-test selection
passed 1,934 tests, including the full ordinary example corpus and all but
one scaling test. The new scoped-variable test needed its binder supplied;
after correcting that setup it passed. The existing conjunction-selection
scaling test timed out under the broad load, then passed alone in 11.6 seconds
under the unchanged 30-second limit. The final seven-test selection passed;
quality checks passed. No limits or budgets changed.

### 8a inventory

Source baseline: `20100ea35` (after package 7 closure). This inventory describes
expression-bearing compatibility paths, not a requirement to eliminate opaque
state, variable, function or allocation identities. The two additional
algebraic slices, 8s.1 and 8s.2, were explicitly approved after this inventory
identified their omission from the original sequence.

| Entry point / payload | Current boundary | Assigned slices |
| --- | --- | --- |
| `kernel_term/boolean.rs`, `KernelTermImport::condition` | Constants, variables, numeric comparisons, Boolean equality/conditionals and calls already have common roots. The fallback wraps the entire other condition in `LegacyBool`. | Views/readers/transport/keys 8b–8f; production and handoffs 8l–8o. |
| `ConditionTerm::{PointerOffsetEqual, PointerEqual, PointerValueEqual}` | Whole native operands inside the Boolean fallback despite package-7 shared pointer support. | 8g, 8h, 8i respectively. |
| `ConditionTerm::{Overflows, BoolLoad}` | Operation/width operands or state/address hidden in the fallback. | 8j, 8k. |
| `ConditionTerm::{AlgebraicEqual, Float32, Float64}` | Native algebraic trees or float comparison/classification operands. | 8r, 8y. |
| `KernelTermImport::argument` | Integer and shared/native machine integers are imported; other `PureFunctionArgument` values use generic `Legacy`. Dedicated pointer routes already bypass this fallback. | Boolean 8l–8o; algebraic 8p–8t; floats 8u–8ab; mixed callers 8ac. |
| `AlgebraicTermNode` | Variable, Constructor, PureFunctionApplication, If and MemoryLoad remain native; Match has package-6 common support but its children can cross this boundary. `ProgramValue::Parameter` carries an algebraic tree too. | 8p, 8s, 8s.1, 8s.2, then 8t; projections/variant reductions 8q. |
| `ProgramValue::{Float32, Float64}` and float `MachineTerm` operations | Float values use native machine carriers; generic imports can hide their operands. Include shared `If`, variables, loads and calls when auditing each float consumer, not only float-specific variants. | 8u–8ab; composition/handoffs in 8aa. |
| Integer, machine, Boolean and pointer call importers | `ApplicationArgument` / `ExactApplicationArgument` preserve exact payload position but can wrap complete nonnumeric expressions. | Family-specific calls 8l/8s/8z, mixed adapters 8ac. |
| `retained_native_machine_operand`, machine importer fallback | Unsupported native expression roots remain exact legacy leaves; migrated numeric, pointer, fold and match routes must retain their established behavior. | Family-specific work above; exhaustive remaining-arm audit 8ad. |
| `machine_observation_leaf`, `bool_observation_leaf`, `native_observation_leaf` | Observation equality is deliberately distinct from exact producer payload identity; the leaf may still contain an expression tree. | Boolean 8f, family-specific consumers and 8ac–8ad; do not erase the identity distinction. |
| `ExecutionValue`, `StoredExecutionValue`, `StoredMemoryValue` | Common numeric/pointer carriers exist; Boolean, algebraic and float handoffs remain native. Memory/temporary carrier keys retain original native equality/order/hash contracts. | 8n–8o, 8t, 8aa–8ab. |

`LegacyIdentity` has Integer, AlgebraicVariable, Machine, MachineObservation,
NativeObservation, ApplicationArgument, ExactApplicationArgument and Fresh
forms. An identity token is not itself an expression migration defect. Inspect
its associated `KernelLegacyTerm.value`: if it hides children, those children
belong to the family slices above. MemoryState identities, binder IDs, type names,
function names and allocation IDs remain legitimate opaque descriptors; keeping
one does not justify retaining an entire expression tree as an opaque payload.
`Void` has no expression children. Array-reference and pointer-integer arguments
must preserve the package-7 descriptors through 8ac, not restart pointer work.

The inventory is a boundary assignment, not completion evidence for the later
slices. Each implementation PR records its actual producer/consumer changes and
checks here; 8ad must reconcile the remaining fallbacks against the final code.

## Chunk 7: complete pointers and read addresses

Deliver 7a–7u sequentially, one PR per slice. Shared offsets are internal
address components with common numeric children, not standalone Click values.
Prepare consumers and existing Surface spelling before switching live producers.
Preserve pointer semantics, exact metadata, evidence, refusals and budgets.
Routine ordering refinements do not change this scope.

| Subchunk | Boundary | Completion criterion |
| --- | --- | --- |
| 7a | Shared offsets | Preserve constant/variable/addition shape, scale, index width and signedness; retain shared numeric children. |
| 7b | Shared addresses | Retain block identity and shared displacement without a parallel native address tree. |
| 7c | Complete pointer payloads | Preserve designation, opaque extent, qualifiers, subobject bounds and evidence, including metadata ignored by logical equality. |
| 7d | Dependency readers | Collect variables, capture and memory dependencies through shared children. |
| 7e | Substitution | Rewrite selected children with capture and metadata preservation. |
| 7f | MemoryState transport | Retain historical read and state identity during transport. |
| 7g | Identity and fact keys | Preserve existing matching keys while separating exact payload identity from logical equality. |
| 7h | Checking consumers | Preserve equality, designation, extent and access evidence requirements. |
| 7i | Address Surface boundary | Raise/lower offsets in their address context using existing syntax. |
| 7j | Complete-pointer Surface boundary | Existing names and spellings retain complete metadata and historical identity. |
| 7k | Scalar read addresses | Numeric loads retain common addresses. |
| 7l | Pointer reads | Pointer/function-pointer loads retain defining memory, address and complete result payload. |
| 7m | Formation and casts | Null/object/function addresses, field projections and casts retain prepared carriers. |
| 7n | Pointer arithmetic | Addition and displacement retain operands and complete metadata. |
| 7o | Numeric observations | Address-to-integer observations and pointer differences preserve existing restrictions. |
| 7p | Pure calls | Pointer-valued specification calls retain their arguments and result structure. |
| 7q | Conditional/match results | Pointer branch assembly retains carriers and scoped obligations. |
| 7r | Locals and call arguments | Assignment, lookup and execution argument handoffs retain pointer structure. |
| 7s | Returns | Callee/caller return handoffs retain complete payloads. |
| 7t | Memory storage | Stores and value receipt preserve pointer structure through the existing memory model. |
| 7u | Closure | Remove superseded pointer adapters; validate nested calls/arithmetic/reads/stores/states and Surface round trips. |

7a prepares a shared offset DAG with constant-time child identities. It is an
internal address component, not a new `KernelType` or source-level value.
Explicit import/export preserves native shape and opaque index annotations;
shared numeric index DAGs are never exported by this boundary. Live producers
remain unchanged until their consumers and pointer-context spelling migrate.

7b prepares raw addresses from shared block identities and shared offsets, with
no parallel native address tree. Block atoms preserve literal occurrence IDs,
loaded-pointer IDs, and exact pure-call payload handles. Call argument migration
remains in 7p. Address identity compares only handles; explicit native output
preserves the original address shape. Producers remain inactive in this slice.

7c prepares complete pointer payloads with shared addresses and common numeric
subobject widths. Qualifiers, designation, opaque extent, object-type evidence
and local-reference custody survive explicit round trips, including metadata
ignored by logical pointer equality. Exact producer handles do not coalesce
those payloads. Persistent evidence is retained without premise traversal;
no live producer or access decision changes in this preparation slice.

7d prepares shared pointer dependency, capture, binder and scope readers. They
visit distinct offset nodes and common numeric children without exporting
addresses or indices. Existing mode-specific treatment of coordinates, loaded
pointer definitions, call arguments and metadata is unchanged; native block
and machine-scope readers are shared with the prepared path.

7e prepares a per-scope structural pointer mapper. Selected address replacements
are simultaneous; shared offset and numeric results are memoized only within
that invocation. Unchanged handles and complete metadata are retained. Numeric
callbacks use the existing scoped term rewriter; no matching search, pointer
normalization, new evidence, or producer activation is introduced here.

7f prepares shared pointer transport across selected memory frames. Numeric
indices use the existing frame checks and scale reconstruction, and shared
addition reconstruction retains the existing constant-displacement policy.
Loaded pointer definitions retain their historical identity; reconstructed
complete words require the same complete-read evidence. All memos are local to
one state/context pair. Native block atoms and one-node scaled adapters remain
explicit compatibility boundaries; shared expression trees are never exported.

7g prepares native/shared state and alpha keys for complete pointers. Offset
keys use compact child identities, cache checked-match requirements, and visit
shared offset DAGs without expanding trees. Numeric alpha keys are reused within
the selected binder context; registered-load traversal keeps the existing depth,
state and refusal policies. Matching keys do not coalesce exact pointer
payloads or supply access evidence. Live pointer producer activation remains in
the later slices.

7h shares the existing origin, extent, access and complete-read fallback policy
between native and common pointer views. Existing checked relations remain the
authority; numeric address aliases cannot supply designation or root-extent
evidence. Shared load-atom comparison visits offset pairs once, preserves the
narrow/wide distinction, and consults load authority even for identical narrow
read roots. Native graph/read adapters remain at the producer compatibility
boundary; no new index, search or evidence rule is introduced.

7i retains numeric indices through address-context Surface spelling for selected
parameter, local and static-array bases. The existing unsigned-32 widening is
inverted structurally; signed-wide indices and other casts keep their carriers.
The local-index reader walks shared children without exporting them and keeps
its existing guard, opaque-call and load-refusal policies. Existing source-name
selection and lowering remain unchanged; offsets gain no standalone syntax.

7j retains complete shared pointer payloads in proof-local source bindings and
raises those bindings through the common-term boundary. Source matching is
separate from logical pointer equality: qualifiers, opaque extents, historical
reads and retained evidence must agree. Matching compares shared children and
persistent evidence identity without exporting numeric trees or walking premises.
Other native source/state readers remain at the producer compatibility
boundary until their carriers switch; this adds no spelling search or syntax.

7k stores shared address handles in numeric read nodes, retaining defining
memory and load kind. Exact call-address payloads remain separate from logical
read equality. Native read admission keeps its existing restrictions; native
atom/storage consumers use the existing cached read-leaf compatibility boundary.
Integer-free and capture readers follow shared addresses with one memo across
nested reads, while binder readers keep reads opaque. Descriptor identity and
nested-read scaling cover shared DAGs without numeric export.
Read registration retains prepared address components at admission, so later
descriptor queries do not re-import them after unrelated arena cleanup. Live
interner hits skip insertion upkeep, and kind-only fingerprints inspect the
shared read directly. Existing search budgets and scaling limits are unchanged.

7l retains pointer and function-pointer read results as common roots containing
the complete result payload, defining memory and shared source address. Read
definitions remain available after producer-registry reset. Native consumers
use an explicit cached compatibility view; lifetime refusals retain their
existing checks. Surface naming preserves complete metadata. Ordinary pointer
formation and arithmetic, calls and storage handoffs remain in their subsequent
slices.

7m admits completed null/object/function address formation, array/aggregate
decay, field-address projections and pointer casts into complete common pointer
roots. Native formation and cast operations retain their existing checks,
qualifier policies and obligations; shared readers and Surface naming consume
the prepared result. The pending-allocation return check accepts that carrier
without changing allocation resolution. Arithmetic and other producer families
remain separate slices.

7n retains pointer addition, subtraction and byte-displacement results with
their original common operand roots, selected stride and complete pointer
payload. Native formation checking still supplies the existing guards, path
facts and refusals through an explicit compatibility boundary. Result
construction and handoffs preserve operand DAGs without exporting them;
Surface spelling and dependency readers retain their prior payload policies.

7o retains numeric pointer address observations with their exact object-class
annotations. Explicit numeric projection of a complete pointer-to-integer value
produces a common observation; its provenance record remains execution metadata.
Numeric observation identity still ignores annotations, while complete-value
transport preserves them. Pointer differences keep the existing same-object/stride
checker and common numeric result admission. Native index admission is unchanged;
Surface observations use the existing pointer cast spelling.

7p retains pointer-valued specification calls as a generic call root with original
common argument handles and the complete result payload. Typed pointer arguments
retain their selected memory state and pointer child; existing nominal
object-type refinement preserves that structure. Explicit native call
argument descriptors preserve object-origin evidence and existing null/projection
reductions. Surface raises the retained generic call with the existing call syntax;
scoped readers keep the native result payload's dependency policy.

7q retains pointer roots through C conditional paths, supported specification
conditionals and selected constructor-match arms. Equal pointer arms keep the
existing complete left payload, including when one input is still native.
Branch facts, guarded obligations and unsupported pointer-match refusals are unchanged.

7r retains complete pointer roots in local storage, assignment, lookup and
ordinary execution-call argument paths. Stored equality/hash/order keep native
pointer identity; declaration qualifiers and entry metadata retain their existing
rules. Callee bindings retain the selected producer after native conversion and
object checks. Builtin/thread argument descriptors remain explicit native adapters;
aggregate copy binding is unchanged. Return conversion and physical memory cells
remain the next two boundaries.

7s retains complete pointers through return coercion, scalar contract-result
bindings and caller result assignment. Modular pointer results enter the common
carrier at their final handoff. Existing const-drop refusals, declared qualifiers,
object-type metadata and aggregate-return ABI/copy behavior remain unchanged.

7t retains complete pointer producers in cached cells, typed union views and
recorded stores. Executed load receipt, local-slot synchronization, aggregate
field/union copies and selected history recovery carry the same root through
existing conversions. Cell equality/hash/order and native diagnostic views keep
the previous payload identity. Logical reads still name their state version;
alias rules, metadata, refusals and history limits are unchanged. Other cell
families remain explicit native payloads.

7u removes the superseded native candidate-selection and union-copy adapters.
Temporary call/operator/prior-assignment results use the same native-key pointer
carrier as memory, so a statement's `StepResult` keeps its producer root. Existing
native result typing, missing-result errors, source names and diagnostic payloads
remain unchanged. Closure regressions cover nested state-read/call/arithmetic
children through temporary results, stores and loads, plus selected-result scaling;
the common-pointer Surface round-trip suite remains part of validation.

Package 7 does not remove all native compatibility data. Pointer checking still
uses selected cached native payloads, complete pointer-carrying integer records
retain their representation metadata, aggregate ABI operations keep their existing
native interfaces, and nonpointer memory families are not migrated by this package.
The remaining packages above own general boundary unification and duplicate
storage removal. No new pointer semantics, syntax, indexes or budgets were added.

## Chunk 6: folds, binders and algebraic matches

Delivered one PR per subchunk, in sequence, preparing scoped consumers and Surface
support before activating new evaluator roots. Preserve existing proof/refusal
behavior, range ordering, binder identity, capture avoidance, scoped obligations
and constructor reduction rules. No new search, indexes or larger budgets.

| Subchunk | Boundary | Completion criterion |
| --- | --- | --- |
| 6a | Common fold payloads | Typed shared children retain range kinds, bounds, initial value, body and exact binder IDs; explicit native conversion is lossless. |
| 6b | Fold scope and dependency readers | Common children support free-variable, capture, binder and memory-dependency collection with correct nested scope. |
| 6c | Fold substitution and transport | Instantiation, rewriting and state transport retain roots and avoid capture. |
| 6d | Fold checking and identity | Existing equality, alpha keys, fact matching and fold rules retain their proofs and refusals. |
| 6e | Fold Surface boundary | Common fold roots raise/lower through existing syntax and certificate paths with exact identity. |
| 6f | Integer fold producers | Actual Integer fold evaluation retains common roots and scoped obligations, including empty ranges. |
| 6g | Machine fold producers | Supported machine folds retain common operands through evaluation and nested arithmetic handoffs. |
| 6h | Common match payloads | Typed scrutinees, ordered arms, bound-field types and bodies; required constructor fields retain common children. |
| 6i | Match scope and transport | Capture-safe dependencies, substitution, rewriting and state handling. |
| 6j | Match checking and reduction | Existing checked constructor selection and equality retain evidence requirements; unknown scrutinees remain symbolic. |
| 6k | Match Surface boundary | Exact raising/lowering and certificate paths preserve arm structure and binding names. |
| 6l | Numeric match producers | Integer and machine result producers retain common arms and roots. |
| 6m | Algebraic match producers | Algebraic result matches retain common structure; other producers have named compatibility boundaries. |
| 6n | Closure | Remove superseded adapters and validate nested folds/matches/calls, fact stability, exact round trips and scaling. |

The following paragraphs record each implementation stage. Later producer
activation supersedes the staging notes in earlier consumer-only steps.

6a ([PR #2731](https://github.com/clicklang/click/pull/2731), merged)
prepares the typed `KernelFold` payload without registering a live
`KernelTermNode` variant or switching evaluator production. This deliberately
keeps new roots unavailable until their scoped readers and Surface support are
ready. Integer results preserve Int32, UInt64 and Integer range kinds; the
existing symbolic machine fold retains its Int32 range and result profile.
This is preparation, not closure of the fold boundary.

6b ([PR #2733](https://github.com/clicklang/click/pull/2733), merged)
prepares common-child readers for Integer-free, expression-free, C-capture
and typed binder variables, plus current-memory read dependencies. Variable
summaries use the existing persistent set representation and a traversal-local
memo keyed by common node identity; filtering body binders never changes the
summary of the same root used as an initial value. Native opaque leaves keep
their existing registry, state and call-connection rules. Dependency queries
retain selected widths and recheck the current state on each call. These
readers remain staged until common fold roots are activated. Validation: nine
focused parity/scaling cases and the full scaling plus related-reader selection
(1,574 tests) pass.

6c ([PR #2734](https://github.com/clicklang/click/pull/2734), merged)
prepares scoped rewriting of the common fold payload. Machine children use
the retained operand walker directly; Integer children reuse the existing
capture-safe fold walker through a rewrite-local, memoized Integer compatibility
bridge. Range endpoints retain shared machine operands, including the existing
UInt64-range/Int32-endpoint carrier convention. The result reports existing
scope/work refusals explicitly. Bounds and initial values stay outside binders,
body rewriting restores the enclosing scope, and pointer substitution preserves
read states. This remains staged until fold roots are activated; the Integer
compatibility boundary has not been removed. All four focused parity/scaling
tests and the full scaling plus rewrite selection (1,682 tests) pass.

6d ([PR #2738](https://github.com/clicklang/click/pull/2738), merged)
shares the machine fold alpha-key implementation between native and common
children. Bound-variable ordinals apply only to the body, with the enclosing
scope restored on success or refusal; free variables and state identities
remain distinct. Integer checking uses a named compatibility adapter retaining
shared endpoints, also reused by scoped rewriting. This does not activate fold
producers or change fold reduction laws. Fold child keys remain boxed so this
variant does not enlarge ordinary scalar keys. The full scaling, related fact
matching/arithmetic, rewrite and registration selection passes 1,676 tests.

6e ([PR #2739](https://github.com/clicklang/click/pull/2739), merged)
adds the existing `.fold(...)` Surface spelling for retained Integer and
machine fold payloads. Body binders use separate Integer/C namespaces;
bounds and initial values stay outside their scope. A single name-freshening
pass avoids capture and processes nested folds iteratively. Integer-index
bounds use existing typed `let` bindings to retain their carrier through
lowering. Round trips compare exact alpha identity, not printed binder IDs.
Concrete machine-fold normalization is unchanged: a rewrite-to-concrete proof
expands and replays without implicit search. This supplies the spelling
boundary; live common fold producer activation remains 6f and 6g. Validation:
the full scaling and related Surface selection passes all 1,634 tests.

6f ([PR #2740](https://github.com/clicklang/click/pull/2740), merged)
activates Integer `KernelTermNode::Fold` roots and the existing Integer fold
constructor produces through them. The evaluator's native Integer result
carrier remains an explicit shallow reading whose operands retain common
handles. Free-variable/capture collection, current-memory dependencies and
scoped rewriting now consume the common fold children; nested summaries filter
only body binders. Internal refusal inspection does not acknowledge a refusal
on behalf of the external rewrite caller. Existing range evaluation, fold laws
and scoped obligations are unchanged. Focused checks pass 25 tests, and the
full scaling plus fold/variable/rewrite selection passes all 1,870 tests.
Opaque endpoints reuse their existing numeric observation identity. The full
non-nightly proof corpus passes with zero fact-stability differences.

6g ([PR #2742](https://github.com/clicklang/click/pull/2742), merged) activates
machine fold roots in native import and specification evaluation.
Symbolic results retain all four common children; concrete evaluation retains
accumulator values between iterations. Scoped collectors, substitution,
checking, alpha identity and numeric observations consume common fold operands.
Pointer-index callbacks distinguish opaque normalization from framed read
transport and capture-safe variable substitution. Existing concrete fold
reduction remains checking-only, and the existing Surface spelling is reused.
Native `MachineTerm` and `CValue` callers remain explicit compatibility consumers;
this does not remove those carriers or introduce a general lambda representation.
Validation: the full scaling and related fold, scope, rewrite, identity and
equality-graph selection passes all 2,113 tests. The full non-nightly proof
corpus passes with zero fact-stability differences. The final correction keeps
ordinary atom selection unchanged outside folds; all 1,849 scaling, fold and
Rust import checks pass.

6h ([PR #2743](https://github.com/clicklang/click/pull/2743), merged) prepares
`KernelMatch`, ordered `KernelMatchArm` and `KernelConstructor`
payloads. Scrutinees, typed binding descriptors, arm bodies and constructor
fields are common handles. Scrutinees and bodies occupy a flat child slice;
binding declarations remain in the corresponding arm scope. Explicit native conversions preserve all three
result families and written binding names. Construction checks representation
sorts only; it does not select a constructor, consult facts or validate proof
evidence. Algebraic children retain the named legacy boundary until activation
in 6m. These payloads are not live evaluator roots until scoped readers and
Surface support are ready. The three focused payload tests and the full
scaling selection (1,566 tests) pass.


6i ([PR #2744](https://github.com/clicklang/click/pull/2744), merged) prepares scoped variable readers, current-memory dependency collection and
capture-safe rewriting for common match payloads. Each arm keeps its typed
binding scope; the scrutinee remains outside it. Readers preserve the distinct
native free-variable, connection, capture and binder-collection policies.
Memory dependencies share one query worklist across common arm bodies, while
rewriting uses the existing carrier maps, freshening and refusal handling.
Machine bodies stay common; Integer and algebraic compatibility boundaries are
explicit. Word variable declarations reify directly without a tree export.
Rewritten algebraic field payloads retain pointer evidence even when ordinary
value equality ignores it. Constructor selection remains the 6j checking step.
The twelve focused native-parity and scaling tests pass. Scope-summary unions
use existing persistent-set differences for similar shared bodies, avoiding
repeated whole-set work when arms bind different variables. The full scaling and
related match, fold, rewrite and variable-collection selection passes all 2,111
tests on this implementation.


6j ([PR #2745](https://github.com/clicklang/click/pull/2745), merged) prepares checked constructor reduction and machine alpha identity for common
match payloads. Native and common reducers share typed field substitution,
including duplicate-binder refusal, pointer evidence and simultaneous capture-safe
replacement. Symbolic scrutinees do not reduce. Machine arm keys use the same
borrowed native/common child walker; unsupported Integer and algebraic match keys
remain unsupported. Reduction and identity retain shared machine bodies rather
than exporting native expression trees. All 1,957 tests in the full scaling and
related match, rewrite and fact-key selection pass, including five new checks.


6k ([PR #2746](https://github.com/clicklang/click/pull/2746), merged)
prepares common match spelling through the existing Surface `match` form.
Ordered arms retain typed C, Integer and algebraic scopes, including nested
folds; written binder names are preferred and conflicting names are freshened.
Common machine bodies raise directly. Private binder markers are finalized
once across the selected output, with arithmetic traversed iteratively to
avoid the reproduced stack overflow on a 128-node match body. This changes
neither language syntax nor evaluator reduction policy. All 2,100 tests in the
full scaling and related Surface, match, fold and substitution selection pass,
including six print/parse/lower round trips and typed-field scope checks.

6l ([PR #2752](https://github.com/clicklang/click/pull/2752), merged)
switches numeric match production to live common roots and arm bodies.
Integer path results retain a shallow native reading; machine path results
retain their `KernelTerm` directly. Scoped consumers preserve capture,
constructor evidence, memory dependencies and typed observation identity.
Ordinary memory transport and fact simplification leave matches opaque,
while explicit substitution visits their scoped bodies. Bool, floating-point
and generic results retain explicit compatibility paths. Algebraic result
production remains 6m; whole-slice closure remains 6n.
The full scaling suite and related match, fold, rewrite, Surface, observation,
memory, condition-decision and variable-reader tests pass: 2,350 total.
Existing Rust signed-match proofs also pass after preserving synthesized
Integer aliases during certificate
observation; the alias is not observed again as a machine value.
The existing false-list refusal keeps its 100,000-unit budget: unchanged
retained word comparisons no longer repeat the same order-fact query. Shared
and native match readers also preserve scrutinee/guard selection, cold-import
observation identity and the existing word-arithmetic dispatch policy.
The full 5,286-fixture Markdown corpus passes with zero fact-stability changes.
Numeric match imports use the same retained-operand boundary as folds: opaque
arm expressions, including boolean casts, remain valid arithmetic leaves.
This fixes the Rust option and example-project storage assertion found by CI.

6m ([PR #2754](https://github.com/clicklang/click/pull/2754), merged)
retains symbolic algebraic match results in a private evaluator carrier.
Nested algebraic scrutinees and arm bodies stay common through construction
and scoped rewriting. Capture reservation walks shared children directly;
unknown nested matches decline constructor reduction without materializing
their native trees. Exact native-source replacement preserves the existing
value-equality policy, including pointer evidence.

Native output is an explicit, iterative compatibility operation. Remaining
boundaries are algebraic constructors and calls, conditionals, equality facts,
resource capture, generic C parameters, and algebraic scrutinee descriptors
consumed by numeric matches. These are not claims that every algebraic term
family has migrated. Concrete constructor selection, arm obligations and
refusals remain unchanged. Producer scaling covers depths 8/16/32/64; scoped
rewriting covers shared nested bodies at 8/32/128 without native exports.
All 2,404 tests in the full scaling and related selection pass, as does the
full Markdown corpus with zero fact-stability differences and the production
build check.

6n removes the superseded `KernelMatch::export_algebraic` adapter. Explicit
output of retained algebraic matches now uses the iterative
`KernelTermExport::algebraic` boundary.
Combined source round trips cover calls around folds, calls inside match arms,
matches inside folds, nested algebraic match scrutinees, and algebraic call
arguments. A deterministic Surface control grows mixed fold/match/call depth
at 3/9/27 and unrelated locals at 0/64/256, requiring no machine exports and
unchanged work as unrelated locals grow. Existing syntax, binder scope,
constructor evidence, refusals and budgets are preserved. All 37 focused
checks and all 2,410 tests in the full scaling and related selection pass. The
full Markdown corpus passes with zero fact-stability differences; production
compilation and the full normal example suite also pass.

Chunk 6 closes the supported fold/match producer and consumer slice. It does
not remove native Integer compatibility readings or migrate algebraic
constructors, calls, conditionals and facts wholesale. Those named boundaries,
plus the remaining result families in chunks 3 and 7–10, remain visible work.

## Chunk 5: execution value handoffs

Retain already-supported machine-integer results through execution, one PR per
slice in order. Preserve proofs, refusals, obligations and search budgets. Other
result families remain in their own packages.

| Subchunk | Boundary | Completion criterion |
| --- | --- | --- |
| 5a | Execution carrier | Reuse the specification value carrier for execution; prepare typed outcome containers and explicit compatibility readers. |
| 5b | Specification handoff | Specification-to-execution adapters retain common roots until an unmigrated consumer explicitly reads them. |
| 5c | C expression handoffs | C expression results retain common machine operands across supported evaluation paths. |
| 5d | Rust expression handoffs | Rust expression results retain common machine operands, preserving Rust operation semantics. |
| 5e | Assignments and locals | Local assignment and readback preserve retained machine results. |
| 5f | Function return handoffs | Return production and caller receipt preserve retained machine results. |
| 5g | Closure | Remove superseded adapters and verify complete supported execution paths. |

5a extracts the existing specification carrier as `ExecutionValue`, retaining
`SpecValue` as a local alias. Expression outcomes and paths accept a value-carrier
parameter, defaulting to their existing native carrier. No producer switches in
this preparatory slice. A deterministic scaling regression checks that repeated
retained handoffs and operand reads do not walk or export growing value DAGs.

[PR #2714](https://github.com/clicklang/click/pull/2714) merged 5a; its pushed
commit was verified upstream. All 1,678 selected checks and all 5,279 regular
fixtures passed, with zero fact-stability differences.

5b retains the specification evaluator's result carrier in resource-child
execution paths. Facts and obligations move with the original result, and the C
fragment route preserves its existing error outcomes. The two resource-schema
consumers make their native compatibility read explicitly at their existing
argument-coercion boundary; coercion and prerequisite rules are unchanged.

[PR #2716](https://github.com/clicklang/click/pull/2716) merged 5b; both pushed
commits were verified upstream. All 1,681 selected checks, 84 integrated Rust and
handoff checks, and all 5,279 regular fixtures passed; the fact-stability audit
recorded zero differences.

5c introduces retained C expression paths. Unsigned arithmetic, supported bitwise
operations and order comparisons consume shared operands directly. Bitwise AND
retains the existing bounded-tag side facts and no-carry requirements; conditional
paths forward the selected result with its facts and obligations. Native
primitive fallbacks keep their existing guards and complete value payloads,
then retain compound machine results. Scalar leaves and other result families
keep their cheap native carriers. Native-only consumers use an explicit output
adapter; local storage and return handoffs are the following slices.

[PR #2718](https://github.com/clicklang/click/pull/2718) merged 5c; its pushed
commit was verified upstream.
Its 1,743 selected checks and all 5,279 regular fixtures passed, with zero
fact-stability differences; final tag/no-carry regressions also passed.

5d forwards Rust shift and supported narrow-arithmetic results through the
execution carrier, using the existing shared producers. Original-width shift
count requirements remain mandatory; only requirements established by the
incoming facts are discharged. Inherited debts are not hypotheses. Unsupported
operator and value families retain their explicit native compatibility routes.
Its 12 focused tests, all 1,633 scaling and Rust import checks, and all 5,279
regular fixtures passed; the fact-stability audit recorded zero differences.

[PR #2719](https://github.com/clicklang/click/pull/2719) merged 5d; its pushed
commit is included in upstream `master`.

5e retains supported machine results in scalar local bindings, assignments,
initializers and checked reads. The stored payload stays exact; local-state
identity uses the existing machine observation key without changing specification
producer equality. Local-name lookup reads retained roots through the existing
held-term index. Ownership, lifetime, initialization, constness and range-fact
checks remain at their existing boundaries. Memory-resident cells, volatile
events, specification C-fragment lowering and unmigrated coercions remain
explicit native consumers. Boolean-cast payloads keep their original native
range-fact producer. All 1,823 affected evaluator, specification, scaling and
example checks and all 5,279 regular fixtures passed; the fact-stability audit
recorded zero differences.

[PR #2722](https://github.com/clicklang/click/pull/2722) merged 5e; its pushed
commit is included in upstream `master`.

5f extends the stored execution carrier to return and exceptional outcomes,
loop return exits and call-result metadata. Return evaluation and same-format
machine result receipt preserve the common root; pointer/aggregate checks and
unmigrated conversions keep their existing native boundaries. The stored
carrier's identity is shared with local storage; specification producer equality
remains exact. Contract lowering and presentation still have explicit native
result consumers. The full pre-integration regular suite passed all 7,492
checks. After integrating upstream's Rust-library and diagnostic changes, all
1,911 affected/scaling checks and all 5,281 regular fixtures passed; the
fact-stability audit recorded zero differences.

[PR #2725](https://github.com/clicklang/click/pull/2725) merged 5f; its pushed
commit is included in upstream `master`.

5g removes redundant native exports when storing machine contract results,
inspecting return-pointer memory and selecting literal completion keys. The
existing literal index still admits the same bounded literal payloads; compound
roots are rejected without exporting their expression prefixes. Complete C
unsigned and Rust narrow-arithmetic paths through logical local updates,
function return, caller assignment and readback retain their roots without
prefix exports and scale across 16, 64 and 256 operations.

At completion of 5g, declared scalar locals still synchronized with native memory
cells (7t subsequently migrates complete pointer cells). Separate
end-to-end regressions keep those declared-local programs and verify that their
returned/local carrier roots survive that compatibility boundary. This sequence
does not migrate memory-cell payloads, unsupported operator/value families,
specification C-fragment consumers or all presentation/certificate storage.
Those explicit boundaries remain part of the wider migration; 5a–5g do not
complete the overall KernelTerm/SurfaceTerm roadmap.

5g passed all 1,929 affected function/contract/return/scaling checks, 87 checks
after integrating the upstream equality-rewrite fix, and all 5,281 regular
fixtures. Its full fact-stability audit recorded zero differences.

## Chunk 4: one producer boundary per PR

Chunk 4 migrates existing numeric producers to retain `KernelTerm` operands and
results. It preserves language semantics, definedness obligations, exact fact
identity, accepted proofs and refusals. It does not add arithmetic capabilities
or redesign proof search.

The previous combined branch is reference material only. Extract and review each
subchunk independently on a fresh branch from current upstream after the previous
PR merges. Do not merge the combined branch or carry its accumulated fixes into
every subchunk. Later chunks remain parked. Each row receives its own PR; split a
row further if it cannot remain a small, independently validated change.

| Subchunk | Producer boundary | Scope |
| --- | --- | --- |
| 4a | Same-type integer casts | Retain identity through casts that do not change integer type; preserve named reads and states. |
| 4b | Signedness conversions | Existing same-width signed/unsigned conversions for 8/16/32/64-bit values. |
| 4c | Widening casts | Existing sign extension and zero extension through 64 bits. |
| 4d | Narrowing casts | Existing truncation and low-word conversions through 64 bits. |
| 4e | Mixed-width arithmetic | Existing integer promotions and usual arithmetic conversions through 64 bits; retain converted operands and results. |
| 4f | Explicit narrow arithmetic | Existing annotated 8/16-bit operations with narrow results, distinct from ordinary promoted arithmetic. |
| 4g | C shifts | Retain operands with independently typed shift counts; preserve C definedness obligations. |
| 4h | Rust shifts | Preserve existing Rust-specific shift behavior and obligations. |
| 4i | Bitwise operations | Existing numeric AND, OR, XOR and NOT, including narrow NOT and required tag side facts. |
| 4j | Supported 128-bit paths | Existing 128-bit conversions and supported arithmetic/bitwise paths; unsupported operations remain unsupported. |

The 4a audit confirms that the existing unary and cast-chain paths already
retain same-type shared integer results. Its PR adds exact-root coverage across
all ten integer formats, registered-read state controls, a changed-type
negative control, and no-export scaling over 16/32/64 casts. Native inputs retain
their existing compatibility boundary. Focused tests and all 1,507 scaling tests
passed; the unchanged `preserve_apply_names_its_missing_viewable.md` passed its
fact-stability audit with zero differences. [PR #2674](https://github.com/clicklang/click/pull/2674)
merged and its pushed commit was verified on upstream.

Subchunk 4b retains already-shared operands in same-width signedness casts at
8, 16, 32 and 64 bits. It preserves the native conversion table's exact written
terms, including inverse 32-bit sign pairs and selected 64-bit extension roots.
Opaque native operands retain shared cast parents after their input boundary;
general calls outside the shared machine fragment keep the compatibility path.
Fixed-size cast-variable comparison guards preserve their native spelling so
cited quotient/remainder bounds continue to match. Tests compare exported terms
against native conversions and check no-export scaling at 16/64/256 casts.
[PR #2677](https://github.com/clicklang/click/pull/2677) merged; both pushed
commits were verified on upstream. All 5,273 regular fixtures and all 1,509
scaling tests passed, with zero fact-stability differences.

Subchunk 4c retains already-shared operands through the 24 widening conversions
among signed/unsigned 8/16/32/64-bit types. It reuses the same selected-root
constructor as 4b, including the native conversion table's generic casts and
32-to-64-bit extension nodes. Exact-term parity covers constants, opaque leaves,
arithmetic, and prior conversion roots; growing-prefix scaling checks retained
children and zero exports at 16/64/256 steps.
[PR #2678](https://github.com/clicklang/click/pull/2678) merged and its commit was
verified on upstream. All 1,511 scaling tests and the regular fixture corpus
passed, with zero fact-stability differences.

Subchunk 4d retains shared results through the 24 narrowing conversions among
signed/unsigned 8/16/32/64-bit types, using the existing generic truncation and
64-to-32-bit low-word constructor rules. Exact-native parity covers boundary
constants, opaque leaves, arithmetic and prior cast roots; 16/64/256-step scaling
checks growing shared prefixes without exports. The existing listed-equality
rewrite strategy also recognizes retained machine observations, preserving the
`snprintf` length proof without changing its source or proof. Expansion/replay,
missing-premise and constant-work admission controls cover that representation
boundary. [PR #2679](https://github.com/clicklang/click/pull/2679) merged; both
pushed commits were verified on upstream. All 1,513 scaling tests and all 5,274
regular fixtures passed, with zero fact-stability differences.

Subchunk 4e retains ordinary arithmetic operands through the existing integer
promotions and usual arithmetic conversions for 8/16/32/64-bit formats. Deferred
addition, subtraction, multiplication, division and remainder reuse the shared
cast constructors and retain their result and definedness obligations. Shifts
keep their separate boundary. Exact native result/domain parity covers all 64
format pairs, mixed native/shared operands, constants and opaque leaves; growing
prefixes check deterministic work and zero exports.
[PR #2680](https://github.com/clicklang/click/pull/2680) merged and its pushed
commit was verified on upstream. All 1,514 scaling tests and all 5,274 regular
fixtures passed, with zero fact-stability differences.

Subchunk 4f retains annotated 8/16-bit addition, subtraction and multiplication
with their existing modular result formats. Operand admission accepts the same
format and fitting unsuffixed int32 literals; other operand types retain the
compatibility path. Literal folding follows the native narrow constructor, and
no new domain obligation is introduced. Exact parity, nested evaluator and
16/64/256-step retained-child scaling tests cover the boundary.
[PR #2681](https://github.com/clicklang/click/pull/2681) merged and its pushed
commit was verified on upstream. All 1,515 scaling tests and all 5,274 regular
fixtures passed, with zero fact-stability differences.

Subchunk 4g retains C-style shift values and independently promoted counts.
Count bounds keep the full wide operand before the operation selects its low
word. Result children use the native importer's operator reading while the
count guards retain the independently promoted type. Signed left shifts keep their nonnegative-value and result-fit obligations.
Shared int64 comparisons reuse the native constructor's root-width bound folding,
so those obligations match the native producer. The affine boundary reads a
false retained disequality as its equality, and certificate source collection
retains the written operands under negation. Tests cover all 64 value/count
format pairs, boundary counts including 2^32, native/shared and opaque operands,
native shared-root identity, explicit bound certificates and expansion/replay,
and deterministic growing value/count chains with zero exports.
[PR #2682](https://github.com/clicklang/click/pull/2682) merged and its pushed
commit was verified on upstream. All 1,517 scaling tests and all 5,275 regular
fixtures passed, with zero fact-stability differences.

Subchunk 4h retains Rust shift operands and results through the existing unsigned
left-shift conversion, signed right-shift promotion and conversion back to the
original type. The count bound uses that original 8/16/32/64-bit width while
sharing 4g's independent count handling. Native term/domain and shared-root
identity parity, nested evaluator/refusal controls and growing chains cover the
Rust boundary. [PR #2683](https://github.com/clicklang/click/pull/2683) merged
and its pushed commit was verified on upstream. All 1,518 scaling tests and all
5,275 regular fixtures passed, with zero fact-stability differences.

Subchunk 4i retains ordinary numeric AND, OR, XOR and NOT through 64 bits,
including their usual promotions, and annotated narrow bitwise operations.
Native mask folding, XOR component ordering/cancellation and double-NOT rules
are preserved. Tag-clearing equalities remain separate side facts; pointer
provenance records retain their explicit compatibility boundary. Alignment
recognition, its bounded certificate reader and the planner accept the retained
mask equality; existing equality keys normalize signed/unsigned 64-bit literals
by their bits. Standard-theorem declaration matching uses the existing exact
proposition identity across native and retained comparisons.
[PR #2684](https://github.com/clicklang/click/pull/2684) merged and both pushed
commits were verified on upstream. All 7,409 non-corpus library tests (including
1,522 scaling tests) and all 5,275 regular fixtures passed, with zero
fact-stability differences.

Subchunk 4j retains conversions involving 128-bit integer formats and the
existing bounded wide arithmetic profile: signed 128-bit multiplication and
same-format signed/unsigned 128-bit division and remainder. Results retain their
mathematical source; overflow and C-defined divisor requirements remain
obligations, never assumed facts. Typed 128-bit reads retain their kind and
state through casts and integer observations. Unsupported wide addition,
subtraction, unsigned multiplication, mixed division, shifts and bitwise
operations remain unsupported. General calls and nonnumeric compatibility
boundaries remain explicit; completing chunk 4 does not complete the overall
KernelTerm/SurfaceTerm migration. Native parity, refusal and state controls,
nested evaluation and two deterministic growth tests pass. All 1,571 selected
regressions (including all 1,524 scaling tests) and all 5,275 regular fixtures
pass, with zero fact-stability differences.

For each PR:

- State the one producer path being migrated and compare its native and retained
  results, including types, casts and ordinary proof obligations.
- Keep existing C and proof fixtures unchanged. In particular,
  `preserve_apply_names_its_missing_viewable.md` must continue to pass.
- Cover positive, refusal and scope/state cases relevant to that path, plus
  no-export and deterministic scaling checks where representation work requires
  them. Run all scaling tests for performance-sensitive changes and the ordinary
  required gate through the repository workflow.
- Fix a blocking representation mismatch at its smallest existing consumer
  boundary. Do not compensate with new search strategies, broader fact indexes,
  increased budgets or altered proofs. If the producer cannot yet preserve the
  existing behavior, retain its compatibility path and reduce the PR scope.
- Record actual validation and merge status. Completion of one row does not
  imply completion of the rest of chunk 4.

## Ordered closure checklist

### 1. Close the remaining checker boundaries — closed

Finish the checker consumers before enabling the remaining shared producers.
The original bounded caller audit was recorded at `fe8c6d931` (PR #2500).
Its specific R1–R7 reproductions were insufficient: disabling the implicit
native conversions at `b247d7499` (PR #2517) exposed additional live callers.
The final pass removes both `SharedMachineIntegerTerm` native conversion traits
permanently, migrates their checker consumers, and makes the remaining output
conversions explicit. Production compilation therefore enforces this boundary.
The closure is the finite checker inventory, not every producer or legacy term
family. A textual accessor occurrence alone is not evidence of a checker dependency.

| Route/group | Evidence and required closure |
| --- | --- |
| Wide comparison dispatch — closed | `decision.rs` sends retained operands to tagged-address reasoning. Residual tag arithmetic stays shared, exact source premises and selected native read transport are preserved, and the dispatcher no longer exports shared operands. Fixed-size atoms and already-native comparisons retain their native rules. |
| Memory-resolution bounds — closed | `recorded_less_equal_candidates` retains operand views and the order index retains original true signed `<`/`<=` source membership. Memory equality reads shared arithmetic and selected native read leaves without exporting endpoints; parity, withdrawal, direction and DAG scaling controls cover this boundary. |
| Mixed operands and reconstruction — closed | R1/R2 source and replacement matching, R5 pointer-index reconstruction and R6 mixed read-evidence matching retain shared operands, including refusal paths. Native evidence comes from selected native leaves or stores. |
| Dependency and atom walkers — closed | Ordinary scalar carriers, selected atoms, shared memory dependencies and R7 pointer-index walkers retain their operands. |
| Output and dead helpers — classified | See the separate boundary inventory below. Native output construction, diagnostics and test references do not establish that a checker inspected a shared tree. |

- [x] Close the memory-resolution endpoint export.
- [x] Close the wide-comparison export after migrating its tagged-address consumer.
- [x] Classify the remaining audit groups and record legitimate native/output boundaries.
- [x] Close R1/R2 opaque source and replacement matching with retained operands.
- [x] Close R3 mixed operation construction with retained native operands.
- [x] Close R4 modular equality projection with retained residue operands.
- [x] Close R7 pointer-index dependency, scope, comparison and fingerprint walkers.
- [x] Close R5/R6 with parity, refusal, no-export and deterministic scaling regressions.
- [x] Remove the obsolete checker adapters and retain no-export regressions.

**Done when:** no checker exports a shared expression to a boxed tree to inspect
it or decide a premise; native/shared rule parity, missing-premise controls and
multi-size scaling checks pass. Explicit output conversion belongs to step 4.
Do not turn this step into another open-ended census repair pass.

#### Final retained checker boundary pass

The starting audit at `fe3690b72` produced 106 diagnostics with native
`Deref`/`AsRef` disabled. Both traits are now removed, and production compilation
passes. Native output callers explicitly request structural output; the old
`scaled_values` traversal is named `native_scaled_values_for_output` and has no
checker callers.

The remaining scaled-index consumers retain operands through:

- Selected-read, root-variable, initialized-byte and guarded-cell inspections;
  signed/unsigned element-bound guards and exact unsigned range membership.
- Scalar and pointer equality rewriting, canonical base-root construction,
  binder substitution, shallow load expansion and equality-fact atom indexing.
- Algebraic scalar-payload traversal, resource-read collection and load
  footprints. Footprints memoize shared nodes by depth, preserving the existing
  depth refusal and source-state/checked-width requirements.
- Arithmetic certificate payload, identity, hashing, translation and alignment
  checks. Occurrence budgets and unsupported-operator refusals remain unchanged;
  a compact DAG does not admit a formerly oversized certificate.
- Wide range-normalization coordinates and candidate keys. MemoryState-sensitive
  memoized fingerprints replace exported endpoint trees; candidates still go
  through the ordinary merge rule. The selected coverage cursor keeps a wide
  displacement without constructing a temporary native range.
- Recorded equality-class input and members. The existing enumeration is
  unchanged, including native source ordering and duplicate handling; it is
  **not** newly classified as a bounded fast lookup. Only its native reference
  adapter remains test-only. Resource-normalization candidate lookup also keeps
  equality-class members retained through its byte/element coordinate keys. Existing scan bans also reject the retained APIs.
- Pointer reassociation: the exact nonoverflow premise is indexed from the
  explicitly cited conditions, with collision verification and no ambient
  lookup. Guard collection still constructs native planner outputs explicitly.

Remaining explicit output boundaries include diagnostic/rendering and Surface
synthesis, native planner segment and instantiation arguments, comparison
prefilter outputs, and the havoc write-set identity producer. These are not
permission to export within a checker; their payload migrations belong to
steps 2–4. Bounded planner comparisons and source-capability inspection also
retain shared operands before applying their existing refusal limits.

Regression coverage includes native/shared behavior, missing and opposite
premises, source withdrawal, certificate size refusal, state and width
checks, and cold repeated-child DAGs at 16/64/256 nodes with no machine exports.
The full local gate passed 7,198 unit/integration tests and all four fixture
harnesses in 11m42s (over the ten-minute target). A subsequent production-only
compile exposed one remaining native equality-class adapter caller in resource
normalization; that caller is migrated above. The final production build passed;
all 1,520 selected normalization, boundary and nonignored scaling tests passed,
as did all 42 documentation tests. Before/after `transport_wide_viewable`
fact-stability runs both passed with zero fact-dependent lowerings. The final
adapter follow-up received these focused checks rather than a second full gate.

#### Checker route inventory

An export below is a call to `KernelTermExport::machine`, including calls made
implicitly by `SharedMachineIntegerTerm::Deref`/`AsRef`. Checking the result of a
shared rewrite and then falling back to `.value()` is still a live export.
Producing another term does not make a route an output-only boundary when the
result already supports shared storage (notably pointer indices).

| ID | Caller and boundary | Reproduction and required closure |
| --- | --- | --- |
| R1 — closed | `proof/term_rewrite.rs`: `TermRewrite::integer` → `shared_machine_operand` → `.value()` fallback; `range_endpoint` has the same pattern. Fast checked substitution, also used by fold instantiation. | Replace a variable inside a shared sum by a native `MachineTerm::If`. The shared replacement importer declines and the entire sum is exported. Retain the exact opaque replacement under shared parents; preserve capture avoidance, carrier types, checked refusals and fold scope. |
| R2 — closed | `proof/equality_rewrite.rs`: `rewrite_with_admitted_equality_as_written` → `rewrite_integer_observation` → `shared::rewrite`; the range-endpoint closure repeats this boundary. Fast exact-equality substitution. | An admitted `x == (if b { 1 } else { 2 })` rewrites the Integer observation of shared `x + x`, but exports the source on shared-import failure. Keep the source shared through replacement construction; test an unavailable source, bound variables, read states and both endpoint formats. |
| R3 — closed | `machine_integer/representation.rs::operation_observation`, called by `identity::machine_operation_of_integer_value`, then `comparison_view_through_integer_operations` and checked consumers such as `ProofFacts::shared_operation_reading`. | One shared arithmetic operand and one native opaque operand miss the both-shared branch; `.value()` exports the shared operand. Retain mixed operands in the common operation node, preserving the existing format map and exact range obligations. All-native construction is a separate legitimate input boundary. |
| R4 — closed | `machine_integer/modular.rs::wrapped_equality_at`, called by `rewrite_with_admitted_equality` after the exact rewrite does not apply. Fast explicit rewrite consequence. | Project `to_integer(shared(x + x)) == 0` to its 32-bit word equality. The projection calls `machine.value()`. Its existing 64-node limit counts outer Integer syntax, not nodes inside a machine observation. Retain residue operands and their comparison, preserving width, polarity and the existing admission/refusal rule; do not increase the limit. |
| R5 — closed | `TermRewrite::offset` → `index_bits` → `structural_value`, then `scaled_int32_node`/`scale_int64`. Fast address reconstruction. | Rename `x` to `y` in an `Int32Scaled` offset containing shared `x + x`. Even a successful shared rewrite exports and reimports the result. The destination offset already stores `SharedMachineIntegerTerm`; retain it directly, preserving stride, signedness and the checked unsigned-index narrowing rule. |
| R6 — closed | `ProofFacts::with_checked_rewritten_loads`: mixed observations take `pairs.push((left.value(), right.value()))`; selected unmatched shared pairs can also reach `rewritten_loads::evidence_operand`. Fast checked presentation/evidence matching. | Compare the observation of shared `x + x` with an opaque native conditional. The match correctly refuses, but first exports the shared side. Keep both views through correspondence/refusal; construct native evidence only at a genuine selected native evidence boundary. Preserve binder independence, original states and exact source authority. |
| R7 — closed | Shared indices inside `PointerOffsetTerm::{Int32Scaled,Int64Scaled}`: variable/capture/binder/scope walkers in `reasoning/variable_collection.rs`; `assumptions::collect_pointer_offset_memory_loads`; related offset equality and memory-blind fingerprint adapters. Fast address/dependency checking. | Passing `value: &SharedMachineIntegerTerm` to an `&MachineTerm` helper invokes `Deref` even without an explicit `.value()` call. Direct pointer-variable collection and current-memory dependency collection both export a shared `x + x` index. Use the existing retained carrier/read/scope summaries and operand views; grow index DAGs and vary state/registry/binder state. No change to pointer semantics is needed. |

The R7 call-site review found `collect_pointer_offset_integer_variables`,
`collect_pointer_offset_capture_variables`, `collect_pointer_offset_scope_summary`,
`collect_pointer_offset_binder_variables`, `collect_pointer_offset_bitvector_variables`,
`collect_pointer_offset_memory_loads`, `offsets_equal_with_load_atoms`, and
`hash_memory_blind_pointer_offset`. These now use retained operands; their tests enter through scaled pointer
indices, rather than only a scalar observation at the root.

**Audit evidence.** Eight temporary kernel probes used a cold shared `int32`
`Add(x, x)` (one operator, one shared variable used twice) and the native
conditional `if b { 1 } else { 2 }`. Every probe recorded **three machine-export
visits**: general opaque replacement, exact opaque replacement, mixed operation
reconstruction, modular projection, shared-offset renaming, mixed read-evidence
refusal, pointer-index variable collection, and pointer-index memory dependency
collection. Counts are expanded node visits, not distinct input nodes. The
rewrite probes checked that the result changed; the operation/projection probes
checked that a result was produced; the read-evidence probe checked refusal.
The last dependency probe had no loads and still exported the index.
Temporary probes are not retained as tests requiring undesirable behavior;
each migration must replace its reproduction with a zero-export regression.

#### Opaque-source and replacement migration

The general and exact-equality walkers now retain an opaque native replacement
under shared arithmetic, including range endpoints. Variable, read and conversion
leaf callbacks use the same exact native-leaf boundary. An unchanged retained
leaf keeps its identity, so an absent source does not manufacture a rewrite.
Cold DAG regressions cover 16, 64 and 256 shared operators in both rewrite routes,
with zero exports and near-linear deterministic work; parity controls cover
whole-expression replacement, missing sources and both endpoint formats.

R1/R2 are **closed**. `proof/machine_source_match.rs` builds query-local
structural keys for the selected source and shared goal. Each shared node is
visited once; parent keys use child IDs, while opaque leaves use the existing
native equality rule. These keys never replace term identities or state
authority. Source imports are retained per carrier; native leaf hashing is
charged, including its payload cost. Neither matching nor a miss exports the
shared expression.

Exact equality rewriting uses the same matcher for its existing canonical-read
comparison. Its numeric address/mask comparison now uses operand views and keeps
its existing operand-order rule. Controls cover changed states, absent
sources, native and shared source inputs, and the deliberate refusal of composite
sources beneath C-item fold binders. Scaling grows both native source length and
shared goal depth at 16, 64 and 256 nodes, for hits and misses in both routes.
The original opaque-source fallback is removed.

R3 is **closed**. Mixed operation construction retains the shared operand and
imports only the explicit native operand. Opaque native composites stay intact
so the checked exact-reading path retains their original observation identity.
The all-native input boundary, format map, literal spelling, unsupported
128-bit operators and exact range premises are unchanged. Controls cover eight
supported formats, both operand orders and all three ring operations, plus
missing lower/upper premises and opaque composite identity. Cold shared DAGs at
16, 64 and 256 operators require constant deterministic construction work and
zero exports.

R4 is **closed**. The bounded modular equality projection carries native or
shared residue operands through construction and uses the shared comparison
view. It never exports an observed shared machine tree. Existing word folding
is reused; narrow operators retain their literal-only folding rule. Width,
equality polarity, the 64 outer-Integer-node limit, and the requirement for an
observation remain unchanged. Native-spelling parity covers all supported
formats, negation, ring operations, repeated and opaque operands; controls cover
refusals and the exact node-limit boundary. A checked equality-rewrite regression
uses a signed observation to rewrite its unsigned residue without export.
Projected equalities explicitly select word substitution in the existing
shared machine walker, including inside signed observations; their shared
comparison storage does not turn them into exact-Integer substitutions.
The arena allocation proof and its reduced regression cover this distinction.
The rewrite consumer recognizes vacuous sign-cast equalities through same-format
shared observations, preserving the distinction from signed/unsigned exact
Integer equality. Its root-only check has cold DAG controls in both orientations.
Cold
DAGs at 16, 64 and 256 nodes have constant projection work and zero exports.
R7 is **closed**. Scaled indices use the shared carrier/read/scope summaries for
variable, capture, binder and current-memory dependency collection. Int32 offset
comparison uses retained operand views and the existing load authority; Int64
offset equality keeps its structural rule. Memory-blind fingerprints use one
encoding for native/shared operands and cached child hashes for shared syntax.
The cache is session-local, keyed by syntax identity, independent of facts,
registry changes and state contents. Controls cover conversion/binder
payloads, registered reads, access widths, changed states and native/shared
parity. Cold DAGs and growing fingerprint prefixes at 16, 64 and 256 nodes have
near-linear deterministic work and no exports.

R5 is **closed**. `index_bits` retains the rewritten machine carrier and
`rebuilt_index` preserves native constant, signed-widening and stride rules
without exporting shared arithmetic. Checked unsigned narrowing still requires
its original selected bound. Native/shared parity covers signed and unsigned
indices, negative/zero/positive strides and resolving versus written forms;
cold doubling DAGs at 16, 64 and 256 nodes stay shared with near-linear work.

R6 is **closed**. Mixed observations use retained syntax correspondence, and
unmatched shared arithmetic remains shared through selected read-equality
checking. Native stored-value evidence comes from the selected store itself;
the existing origin-chain rule accepts retained endpoints. Binder restrictions,
read widths and state/source authority are unchanged. Controls cover opaque
mismatches in both directions, explicit source withdrawal, stored values,
unchanged origins and intervening writes. Multi-size cold mismatch controls
refuse without exporting or walking the shared arithmetic DAG. Existing
read-evidence tests still recheck authority after syntax-cache reuse.

#### Cleanup compiler audit — remaining conversions inventoried

Temporarily removing `SharedMachineIntegerTerm`'s `Deref<Target = MachineTerm>`
and `AsRef<MachineTerm>` implementations exposes implicit conversions that
text searches missed. The `fast-gate` test build reports both production and
test consumers; a diagnostic is not automatically a distinct checker gap.
The traits cannot yet be deleted. In particular:

- `PureFactContext::pointer_offset_congruence_evidence` now retains shared
  scaled indices through exact/direct bitvector evidence, additive cancellation,
  selected-source indexing and existing evidence checking. Offset linear forms
  retain shared leaves, including the residue test used to construct an offset
  equality. Surface certificate construction still has explicit native output
  getters; `scalar_evidence_class` still returns native terms to other
  consumers. `single_scaled_index_equal_to_constant` likewise still exposes a
  native index to the remaining order-path/condition-construction callers.
  Those compatibility boundaries are not closed by this increment. The native
  class API preserves syntax-sorted candidate order. Unsupported Integer
  equalities must be rejected before recording pointer-coordinate dependencies;
  they contribute no source edge and must not disable memory-query shortcuts.
- Contract certification now retains indices through byte bounds, additive
  endpoint construction, shallow binder-coordinate collection and selected
  read/cell equality. `contract_claims.rs` selects a read leaf directly. The
  checking-only simplifier memoizes shared DAG nodes; it does not change lowering.
- Difference-graph offset equality/residue, variable-chain index recognition,
  alignment factor inspection, store-gap roots and scope roots use operand views.
  Memory/binder walkers select retained leaves; memory provenance preserves
  first-occurrence candidate order. Proof-fact atom collection reuses its shared
  collector. Load-presence queries use syntax summaries, without enumerating
  growing free-variable sets.
- `PointerOffsetTerm::{for_each_scaled_value,any_scaled_value}` have no callers
  and are removed. The retained alternatives are `for_each_scaled_operand` and
  `any_scaled_operand`. `scaled_values` remains at native diagnostic/test
  boundaries; checker root queries use `scaled_operands`.
- Live at the contract-certification checkpoint (superseded below): native
  byte/element reconstruction in `reasoning/path_facts.rs`,
  exact-rebuild and selected-index order checks in `condition_reasoning/order_paths`,
  plus native consumers in `assumptions::{memory_reasoning,proposition_reasoning}`.
  `scalar_evidence_class` and `single_scaled_index_equal_to_constant` also retain
  their native outputs. These routes must migrate before removing the implicit
  traits; the contract increment does not close the entire cleanup audit.

This cleanup increment removes `map_scaled_values`, replacing it with a
shared-operand mapper. Equality-graph affine keys, offset interning, read-offset
classification and four-byte scaled-word source indexing retain their inputs.
Offset equality follows the existing shared-input policy: shared syntax and
read states retain their identity; genuine native inputs take the legacy
comparison form before locking. No-export controls cover width/signedness,
source polarity/withdrawal, sibling contexts, state identity and cold DAGs.
Validation: all 12 focused tests and the full gate passed (7,733 unit/API tests,
58 examples, 5,123 mdtests). The gate took 11m06s and emitted its existing
ten-minute budget warning; no limits changed.

The offset-evidence increment passed the full gate: 7,742 unit/API tests,
58 examples and 5,123 mdtests, including the unchanged duplicate-reference
refusal. The gate exited 0 in 14m18s (the environment restarted during the run,
but the process survived), with its existing ten-minute warning and no limit
changes. A separate combined scaling/focused run passed 1,415 tests before the
final dependency-bookkeeping fix; the final gate reran the scaling tests. Cold
success/refusal controls at 16, 64 and 256 operators require zero exports.

**Validated cleanup:** the contract-certification and retained walker
increment includes no-export, state/source-withdrawal and DAG scaling
controls. Direct scalar-to-literal support is indexed on admission so a native
written equality and its shared operand query use the same source; this does
not permit transitive equality to substitute for a direct premise.

Validation: 50 focused arithmetic/loadability tests passed, followed by 72
focused difference-graph/contract tests after preserving the full-bit reading
of unsigned wide literals. The full `scripts/check.sh --no-fail-fast` gate
exited 0: 7,086 unit/API tests and all four fixture phases passed. It took
12m31s and emitted the ten-minute budget warning; no limits changed and no
nightly suite ran. The unrelated-block scaling test now creates a fresh
verification session per sample, retaining its exact work-equality assertion
instead of comparing one cold sample with two warmed samples.

The repeated production-library trait-removal audit reports 194 diagnostics
(previously 216); neither contract certification nor the difference graph
appears in it. This is a compiler-location inventory, not a count of remaining
checker routes: it also includes native outputs and diagnostics. The temporary
trait removal was restored byte-for-byte. The live exact-rebuild calls in
`condition_reasoning/order_paths.rs` and the Integer carrier scope call in
`spec.rs` are explicit next targets alongside the reconstruction services.

**Byte/element reconstruction increment:** `shared_byte_offset_from_pointer_offset`
and `shared_element_index_from_offset_with_facts` retain the index DAG while
building the same residues. The existing shared element builder is also the
implementation behind the native-output adapter. Full-width constants and
range evidence still control wide-to-word projection; low-word evidence,
unsupported widths and missing bounds do not suffice. The wide-equality
adjacency index now accepts retained query keys while preserving the native
syntax order of its source buckets.

Offset equality decision, offset-derived scalar path facts and exact-rebuild
checks consume those shared results. `single_scaled_index_equal_to_constant`
returns the retained index. Add/multiply exactness uses the existing shared
overflow query; accepting equal residues still requires exact rebuilds, while
unequal residues can refute equality without that premise. The obsolete native
signed-wide bound wrapper is removed. The difference-graph dispatcher routes
retained machine-order comparisons through its existing shared order checker;
this preserves full-width subtraction bounds and byte-array address proofs.
Native literal outputs bypass the general exporter, preserving the existing
per-cell store-work budget. Ambient-fact scaling tests use a fresh session per
size so cold and warm syntax caches are not compared. The fork/join sidecar
now proves its `range_filled` bridge by introducing the index and bounds,
instantiating the returned range fact, then rewriting the job fields. Those
simple steps pass on retained operands; the previous implicit closure exhausted
its unchanged work budget after the comparison representation changed. The C
program and claims are unchanged; no search fallback or budget increase was added.

At this checkpoint the native-output adapters remained live in memory resolution
and range checks, together with shallow scalar comparison/exact-constant queries
and `ExactElementDelta`'s native index field. The following increment migrates
those routes. The Integer carrier scope call in `spec.rs` remains separate work.

Validation: `scripts/check.sh --no-fail-fast` passed: 7,094 unit/API tests,
58 example projects, and 5,130 mdtests, including the scaling regressions.
Focused coverage includes missing/withdrawn full-width bounds, low-word-only
refusal, overflow refusal, and zero-export growing-DAG checks. The gate took
10m08s and emitted its ten-minute-budget warning; no limits were increased.
No nightly suite was run.

**Memory-resolution and range-index increment:**
`ExactElementDelta.index` and its single-index projection now retain shared int32
operands; the separate exact `i64` constant and the refusal to combine two
symbolic indices remain. Membership, exclusion, shifted-range coverage,
byte-gap checks, and exact rebuild comparisons consume operand views. The
literal-source index accepts retained input keys and preserves original premise
order. Affine index comparison visits a shared DAG once, propagating coefficients
without exporting or expanding repeated subexpressions.

Resource coordinate keys, selected range evidence, pointer-formation bounds,
and contract/loop range checks keep those operands. Range splitting retains
shared intermediate endpoints through its checks and exports only when creating
native `CMemoryRange` output bounds. MemoryState comparisons still enter the native
memory machinery only through selected read leaves. The unused native byte-offset
adapter and several obsolete checker wrappers are removed. Native pointer-index
output APIs still serve native resource/value producers and Surface tools; this
increment does not claim to remove every native carrier in the kernel.

Shared scalar equality admission retains its own replayable graph input rather
than reconstructing the equality through Integer observations. Read-equality
deltas preserve those inputs too. Selected comparisons reuse original native
bound sources; atomic read leaves enter their existing scalar comparison route.
Empty bounds indexes return immediately, and pointer-distinctness queries share
their existing resolution memo across the nested scalar checks.

The negative branch-interface fixture now explicitly rewrites its established
`k == 0` before combining the preserved-cell bounds. Its C, claims, and expected
definedness rejection are unchanged; the original omitted proof reached its
unchanged smart-search budget. No search fallback or limit increase was added.

Validation after rebasing onto current master: `scripts/check.sh --no-fail-fast`
passed: 7,109 unit/API tests, 58 example projects, and 5,146 mdtests. New tests cover exact-delta retention,
missing and withdrawn bounds, large constants and wrap refusals, zero-export
shared-DAG growth, and scalar-input replay with read-equality deltas. Existing
scaling tests compare fresh verification sessions at each size, retaining their
original limits. Focused fact-stability runs for the vector-prefix and negative
branch-interface fixtures passed with zero report entries. The rebased gate took
9m53s, within the ten-minute budget. No limits were increased and no nightly
suite was run.

#### Boundary audit after the memory/range increment

Repeating the production-library compiler audit with both implicit
`SharedMachineIntegerTerm` native traits disabled reports **178 diagnostics**
(previous checkpoint: 194). The temporary change was restored byte-for-byte.
This completes the inventory pass, **not** removal of every checker boundary.
The remaining locations divide into these concrete groups:

| Group | Remaining routes | Disposition |
| --- | --- | --- |
| Read/address checking | `memory_resolution` offset matching, exact-index materialization and selected read payloads; `memory_provenance` framed transport and exact-load normalization are closed below | Live checker migration; shared outer arithmetic does not eliminate native address children |
| Wide indices and shallow pointer checks | Wide access reconstruction, strided-region membership, offset transport and fold-read summaries are closed below; state equivalence and `pointer_block_bounds` remain | Retain width, signedness and exactness rules while closing the remaining callers |
| Pointer fact/rewrite payloads | `arithmetic_special`, `equality_rewrite`, `fact_reasoning`, pointer-offset substitution and execution facts; state-blind and alpha pointer-index fact keys are closed below | Mixed construction/checking boundaries; migrate expression children without changing pointer semantics |
| Resource and state construction | quantified cells, memory-base roots, initialized-byte spelling, havoc identity, memory-load range collection | Mixed producer/checker boundaries, not merely printing |
| Native outputs and Surface tools | final `CValue`/`CMemoryRange` bounds, Surface synthesis/certificates, diagnostic renderers, planner segment indices | Explicit output or frontend/tool boundaries; remove only with their corresponding payload migration |

`scalar_evidence_class` is still a native syntax-sorted alias enumeration API.
Its callers include selected stored-value recovery, memory-base/root matching,
C operand simplification and a test-only reference inconsistency scan. It is
not a general shared arithmetic decision API, and must not be relabelled as
printer-only. `single_scaled_index_equal_to_constant`, in contrast, now returns
a retained index. `element_index_from_offset_with_facts` has only test callers;
production uses the shared helper. The conservative `integer_carrier_in_integer`
query already uses operand views and has no-export coverage; the distinct
`integer_carrier_in_pointer_offset` query remains in the compiler inventory.

At that checkpoint the residual traits could not yet be removed; the final
retained checker pass above removes them. Nested signed construction below
is independently guarded by zero-export and growth tests: its arithmetic and
obligations retain shared roots, with one final native value output at the
existing evaluator boundary. This does not declare step 1 or the complete
KernelTerm/SurfaceTerm split finished.

#### Retained pointer-index checks

Strided-region field checks pass operand views to their existing bound checker,
including the range-evidence caller; they no longer construct a native index
between selecting a stride and checking its bounds. Parameter partition roots,
open-side classification, and pointer-offset Integer carrier scope checks inspect
only the retained root. Pointer-offset transport uses the existing shared
transport checker. Mixed signed-word/unsigned-wide offset equality observes its
retained operands directly, and unsigned-wide index equality constructs a shared
comparison.

Fold-read offset summaries retain shared int32/int64 atoms and return a shared
scaled index. Their membership/exclusion checks use the existing selected exact
comparison source index, preserving strictness and missing-bound refusals. This
removes the native index storage from the summary itself; native interval bounds
remain input/output boundaries. Cold index DAGs at 16, 64 and 256 nodes have
constant summary-query work and zero exports. Focused controls cover stated and
missing bounds, both bounds of a strided field, and existing frame/refusal rules.

This increment closes those named consumers, not wide access reconstruction,
read-address payload normalization, state-equivalence recursion, or the
remaining native pointer rewrite/fact-key families. The implicit native traits
remain until those callers migrate.

Validation: all 39 focused tests passed, then `scripts/check.sh --no-fail-fast`
exited 0 with 7,115 unit/API tests, 58 example projects and 5,149 mdtests. The
gate took 9m29s, within budget. Existing fold-read transport fixtures passed
before and after with zero fact-stability entries. No limits changed and no
nightly suite ran.

#### Shared wide access coordinates

Wide element-index reconstruction returns a retained operand. Its consumers in
range membership/separation, selected-source loadability, scalar writes and
translated range coverage check that operand directly. Full-width observer
equality inspects selected read leaves and existing exact equality neighbors;
it does not export an arithmetic prefix to find a load.

The former native wide-index helpers are removed. Existing signed extension,
nonnegative coordinate reconstruction, no-wrap guards, missing-bound refusals
and alias candidate order are preserved. Range rebasing retains the access
coordinate through its endpoint construction. `CMemoryRange` still stores native
endpoints. The `checked_native_range_endpoint` and `wide_range_bound_pair`
adapters also retain native checking callers (same-base coverage, alias-overlap
and pointer-formation checks, and split/merge decisions); those callers must migrate before these
adapters can be classified as output-only or removed.

Controls distinguish a full-width bound from a bound on the truncated low word.
Cold doubled index DAGs at 16, 64 and 256 levels reconstruct with constant query
work and zero exports. This closes the wide access reconstruction group above,
not read-address normalization, state recursion, pointer rewrite/fact keys,
or generic native expression bridges.

The nested-rounding bound rule is shared by native and retained comparisons:
`(a - a % k) <= upper` needs a nonzero `k` and `a <= upper`. It follows
the dividend chain without exporting shared prefixes. Its old native form
incorrectly used a non-strict premise for a strict conclusion; the shared rule
refuses that inference. Controls cover the counterexample where rounding eight
twice by four still gives eight, missing/zero divisors, and growing shared
rounding chains. Literal coordinate construction and arithmetic use direct
paths so native-loadability queries have the same cost in cold and warm runs.

Validation: 88 focused tests passed. `scripts/check.sh --no-fail-fast` exited 0
in 9m17s: 7,125 unit/API tests, 58 example projects and 5,160 mdtests passed.
The two wide-range transport fixtures and the nested chunk-tail fixture passed
with zero fact-stability entries. The strictness counterexample and the missing
shared bound both failed before the common-rule fix and pass afterward.
No nightly suite ran.

#### Retained wide endpoint checks

The native endpoint/rebasing adapters listed above are removed.
`shared_wide_range_bounds` and `shared_rebased_wide_bounds` retain their
coordinates through same-base coverage, alias-overlap checks, pointer formation,
and split/merge decisions. Translated-window checking receives the selected base,
width and retained bounds directly; it does not need a temporary resource
containing exported endpoints.

Split and merge convert endpoints only when constructing their final
`CMemoryRange` outputs, preserving the original range carrier metadata. Native
endpoint storage and native normalization/fact keys remain separate boundaries;
this does not classify those consumers as migrated. Controls cover complete
versus truncated bounds, 64-bit split/merge outputs, and cold rebasing DAGs.

Validation: all 46 focused tests passed. `scripts/check.sh --no-fail-fast`
exited 0 in 9m14s: 7,128 unit/API tests, 58 example projects and 5,160 mdtests
passed. No nightly suite ran.

The production compiler audit after this increment reports 157 primary error
locations with the two implicit conversion traits disabled, versus 178 at the
previous checkpoint. These are caller locations, not distinct checker defects;
output, diagnostics and native payload construction also depend on the traits.
The traits were restored after the audit. After the cell-run and wide-offset closures below, remaining checker examples
include read-address/state reasoning, pointer fact keys and native range
normalization.

#### Retained cell-run access indices

`RunAccess::Scaled` and `ScaledWide` retain the pointer's shared index instead
of materializing a native index in an intermediate access record. Exact-slot
lookup, store-window intervals and symbolic run loads use existing shared
constant/interval/comparison queries. They preserve exact 64-bit evidence,
missing-evidence refusal, slot holes, access widths and path exclusions.
The structural constant readers in offset atom collection, stride differences
and exact byte shifts also inspect retained operands.

Controls cover pinned and unknown slots, holes, signed 32-bit constant
interpretation, and cold repeated-child DAGs at 16, 64 and 256 levels without
machine exports. Native read-address normalization remains separate; the
stepped wide-offset equality route is closed below.

Validation: six focused tests passed. `scripts/check.sh --no-fail-fast` exited
0 in 9m24s: 7,132 unit/API tests, 58 examples and 5,160 mdtests passed. Both
wide-range transport fixtures passed with zero fact-stability entries. No
nightly suite ran.

#### Retained wide offset equality

The unsigned-64-bit constant and stepped-index routes in
`pointer_offsets_equal_for_memory_resolution` now retain their index operands.
The stepped route constructs its addition with `wide_index_binary` and uses
shared comparisons, preserving its complete-width no-wrap guard. Exact
constant evidence is read through `wide_constant_from_equalities_view`, with
the same equality directions and query order. A matching low word alone cannot
pin the full index.

Controls preserve the full high word, signed byte-offset refusals, misalignment,
missing no-wrap premises and wrapping increments. Cold shared DAGs and unrelated
fact populations exercise the same selected equality route without exporting
index trees. Read-address/state reasoning, pointer fact keys and native range
normalization remain separate checker boundaries.

Validation: the full `scripts/check.sh --no-fail-fast` gate exited 0 in 9m01s:
7,135 unit/API tests, 58 examples and 5,160 mdtests passed. After rebasing onto
current master and reducing only the unrelated-fact test multiplier, all six
focused tests passed. The final growth test took 0.184s, retaining its three
DAG sizes and work/export assertions. No nightly suite ran.

#### Retained pointer-index memory evidence

`pointer_offsets_match_from_memory_derivations` uses the existing shared int32
value-equality and explicit memory-derivation queries for scaled indices.
`pointer_offset_equality_evidence` and its typed checker select read sources
through operand views instead of exporting shared arithmetic merely to inspect
its root. The native atomic evidence checker still enforces its read-root,
width and exact-state requirements; this does not broaden its rule family.

Controls compare native/shared value answers, preserve changed-cell and width
refusals, and reject cold arithmetic DAGs at 16, 64 and 256 levels with constant
root-inspection work and zero exports. Framed pointer-offset transport and
exact-load normalization are closed below. The implicit traits and other live
checker migrations listed above remain open.

Validation: five focused tests passed. The full `scripts/check.sh --no-fail-fast`
gate exited 0 in 9m17s: 7,138 unit/API tests, 58 examples and 5,160 mdtests
passed. The subsequent rebase adds only an unrelated CLI change; no tested
kernel source changed. No nightly suite ran.

#### Explicit native address-walker boundaries

The four canonicalization/read-selection walkers explicitly borrow retained
native inputs after their shared-index guard. These eight call sites no longer
depend on implicit `Deref`. Shared indices retain their exact structure and
states without entering the native walkers. This classifies existing native
input paths. Framed transport and exact-load normalization are closed below.

Validation: `scripts/check.sh --no-fail-fast` exited 0 with 7,142 unit/API tests
and the complete regular examples/mdtests. The cold run took 14m07s, including
3m48s compilation, and exceeded the ten-minute budget. A redundant standalone
documentation build was stopped after it competed with the fixture phase;
rendering and lint had completed. The unit phase took 276s versus 273s in the
previous gate. No limits changed and no nightly suite ran.

#### Retained pointer-formation bounds

Recorded-block formation checks retain scaled indices through signed/unsigned
wide comparisons and the signed extension of a 32-bit coordinate. Exact byte
coordinate reconstruction retains intermediate sums and products. Its signed
range requirements are ordinary Integer upper/lower bounds; unsigned indices
still need the full-width maximum-index guard before signed interpretation.
Opaque byte-offset variables and negative unsigned strides keep their refusals.
The coordinate constructors preserve native constant-reading and product
zero/one rules; they do not apply comparison-only simplifications to values.

A native/shared parity test exposed extension constant metadata that folded a
computed narrow operand where the native reader accepts only a literal of that
width. Shared metadata now preserves those literal requirements, including the
signed-to-unsigned wide extension. Retained native leaves supply their existing
constant reading once on introduction, including literal-conditioned native
conditionals; shared parents reuse the result. This is checking metadata, not a
change to structural lowering. Controls cover exact constructor shapes,
overflowing and full-width coordinates, missing bounds, read states and
growing DAG prefixes.

The full gate exposed a common comparison-reader gap: removing an exact
extension could leave different observation formats and lose the original
common-format comparison. The reader now retains that written view when the
value reading cannot form a machine comparison. The existing mixed `int` /
`size_t` allocation-index fixture verifies unchanged, with zero fact-stability
differences; a unit regression covers separate bounds and missing premises.
Validation: `scripts/check.sh --no-fail-fast` passed in 9m49s with the
precompiled test binary: 7,150 unit/API tests, 58 example projects and 5,180
mdtests. The focused eight-test run includes deterministic 16/64/256-prefix
scaling and zero-export checks. No nightly run.

The distinct cumulative pointer-index producer and remaining compiler-audit
groups are still open. Framed transport and exact-load normalization are closed below.

#### Retained state-equivalent pointer indices

The state-equivalence route for 32-bit scaled indices now retains operand
views. Its shared syntax correspondence is cached separately from proof
authority: every selected read pair is checked under the current context.
The existing native rule remains the reference: exact syntax matches, and
changed read states may be framed only through same-format 32-bit sums,
differences and products. Casts, other operations and wide arithmetic retain
exact-syntax matching but do not gain framing of changed reads. Variables do
not acquire registered-load semantics in this route.

The state source index shares the native/shared operand fingerprint walker.
Its policy omits read addresses and states only along those same permitted
paths, while the existing memory-blind fingerprint retains its own policy.
This also aligns the source-index shape with the existing unsigned 32-bit ring
comparison rule; previously the shape recognized only signed ring operations.
These fingerprints select candidates, never prove equality.

Validation: four focused tests pass, including native/shared and mixed parity,
source lookup in both orientations, withdrawn/missing premises, branch-context
authority and deterministic 16/64/256-prefix growth with zero exports.
`scripts/check.sh --no-fail-fast` passed with 7,154 unit/API tests, 58 example
projects and 5,180 mdtests. Its precompiled-binary run took 10m04s and emitted
the ten-minute budget warning, versus 9m49s for the preceding checkpoint;
no limits were changed and no nightly suite was run.

#### Remaining index-query adapters

Wide unsigned-index distinctness compares retained full-width operands,
including a constant byte displacement beside a scaled index. Mismatched or
nonpositive strides retain their previous refusal, and neither operand is
truncated to a low word. Exact scalar-constant substitution uses the existing
operand-view equality index and still requires the byte product to fit.
Shallow index equality calls the maintained graph through operand views.
Plain-origin classification reads only the root variable or literal and keeps
its existing accepted literal formats; computed constants remain nonplain.

The new controls exposed two shared-route gaps. Exact-constant source admission
now files written 32/64-bit machine observations as well as native comparisons,
retaining the original source condition and endpoint syntax. The contextual
wide-constant evaluator now memoizes completed shared misses by fact identity,
logical-read generation, node identity and evidence-capture mode. Positive
answers retain their existing source-evidence path; cycle/depth cuts mark the
incomplete-reasoning epoch and do not become completed negative entries.
The growing-prefix probe fell from 40,938 / 227,706 / 1,504,680 work units to
35,820 / 151,932 / 616,380 at 16 / 64 / 256 prefixes. Temporary call-site
profiling was removed from the source.

The compiler-assisted audit at `bef90e92c` temporarily disabled the implicit
`Deref`/`AsRef` tree conversions and found 120 primary locations, compared with
157 in the earlier endpoint audit. These include diagnostics, synthesis and
native output construction, not just checker dependencies. The traits were
restored after the audit; this count is a boundary inventory, not a claim that
all those sites are defects or that step 1 is closed.

Validation: all 11 focused tests pass, including deterministic growing-prefix
checks with and without evidence capture and zero tree exports.
`scripts/check.sh --no-fail-fast` passed with 7,158 unit/API tests, 58 example
projects and 5,180 mdtests in 9m41s with the binary precompiled. No limits
were changed and no nightly suite was run.

#### Exact-materialization index equality

The assumption-free offset comparison retains its indices while following only
root `int32` reads through exact stored cells. It does not normalize loads inside
arithmetic, reinterpret other read kinds, or resolve an unknown state. Both
sides are materialized once; the existing bounded state rule then receives
only selected native read leaves. Exact shared syntax correspondence reuses the
memoized operand matcher with framing disabled, preserving native literal and
operator distinctions without exporting either arithmetic DAG. This is also the
syntax-equality primitive needed by the remaining shared reconstruction work.

Validation: five focused tests pass, including native/shared/mixed parity,
root-only and kind refusals, separated/overlapping stores, havoc and cold-session
16/64/256-prefix scaling with zero exports. The full gate passed 7,161 unit/API
tests, 58 example projects and 5,180 mdtests. Its precompiled-binary run took
10m09s and emitted the ten-minute budget warning (preceding run: 9m41s). The
extra wall time was distributed across existing tests; the five focused tests
took 0.043s. This does not establish a cause for the variation. No limits were
changed and no nightly suite was run. Full exact-load normalization is closed
in the later increment below.

#### Framed pointer-index transport — closed

Framed transport retains shared scaled indices through memory updates. An
iterative, query-local walk visits each distinct arithmetic node once and
rebuilds shared children. Only selected native leaves enter the existing
memory-framing checks; no proof authority is cached across contexts or states.
Native inputs still use the native walker. Raw 32-bit operators, wide constructor
constant readings, casts, stride simplification and the offset carrier convention
retain their existing rules. Opaque leaves retain their existing transport
refusals; this does not add a new memory equality rule.

Six focused tests pass, covering constructor parity, opaque constant readings,
registered load names, changed and unknown states, overlapping stores, havoc,
and refusal paths. Cold repeated-child DAGs at 16, 64 and 256 nodes retain
near-linear deterministic work with zero machine-tree exports through the actual
pointer-offset entry point, for signed 32-bit and signed/unsigned wide indices.
The broader selected run passed 1,713 tests, including all nonignored scaling
tests, memory provenance, rewriting, transport API, documentation and search
boundaries, using the gate's existing 8 MiB test-thread stack. Formatting and
documentation rendering passed; advisory Vale lint was unavailable. The full
integration gate and nightly suite were not run locally; CI and the merge queue
run the full gate. The complete split remains open.

#### Exact-load normalization of pointer indices — closed

Exact-load normalization now uses the same iterative, query-local shared-index
walk as framed transport, with its own smart-constructor policy. It resolves
selected native load leaves through the existing state/kind checks and
cycle guard, and retains shared arithmetic parents. Native inputs and opaque
selected leaves keep the native normalizer. Load authority never survives a
query or fact-context change. The narrow carrier, signed/unsigned wide reading,
stride reductions, and 32-bit smart folding (including sorted XOR cancellation)
retain their native rules. XOR orders selected atoms structurally without
exporting their shared arithmetic; rebuilding its normalized chain charges work
for the selected atoms and produced nodes.

Validation: all 1,721 selected tests passed on the rebased change, including all
nonignored scaling tests, memory provenance, equality/term rewriting, transport
API, documentation and search-boundary checks. The run used the existing 8 MiB
test-thread stack; compilation took 5m07s and tests took 116s (two slow notices).
The five new regressions cover native constructor parity, state/kind/context
authority, and cold 16/64/256-node DAGs for unchanged arithmetic, resolved read
children and structurally ordered XOR atoms, with zero machine-tree exports.
Formatting and documentation rendering passed. The full integration gate and
nightly suite were not run locally; PR CI and the merge queue run the full gate.
The remaining compiler-audit inventory, producers, legacy families, and final
Surface/Kernel boundary remain open; this closes pointer-index normalization,
not the whole migration.

#### Retained pointer-index fact keys — closed

MemoryState-blind pointer-offset keys consume the retained machine operand view,
using the existing interned syntax keys instead of exporting an index tree.
Both narrow and wide scaled offsets preserve their stride and unsigned reading.
These keys still select candidates only: erasing a read state never supplies
proof authority.

Alpha pointer-offset keys now retain the existing compact machine-key DAG,
including exact proposition identities and quantified candidate keys. Selected
native leaves keep their existing binder, load-kind, registry and state rules.
Binders introduced inside an opaque machine leaf use leaf-local ordinals: a
repeated DAG child and repeated native syntax agree, while outer binders,
shadowing and free variables remain distinct. No load answer or binder-context
result is cached across queries.

Validation: all 1,796 selected tests passed, including every nonignored scaling
test, proof fact/key/reasoning tests, equality/term rewriting, transport API,
documentation and search-boundary checks. Seven new regressions cover native
syntax parity, repeated opaque binders, shadowing/free-variable distinctions,
stride/signedness, state/kind authority, and actual fact-store hit/miss and
branch behavior. Cold 16/64/256-node DAGs and growing state-key prefixes have
near-linear deterministic work with zero exports; lookup work stays bounded
beside 16/64/256 unrelated facts. Compilation took 1m36s and tests took 110s
(two slow notices), using the gate's existing 8 MiB test-thread stack.
Formatting and documentation rendering passed. The full integration gate and
nightly suite were not run locally; PR CI and the merge queue run the full gate.
The remaining checker inventory, producer migrations, legacy term families and
final common boundary remain open.

#### Classified boundaries and retained coverage

- `variable_collection::visit_machine_carrier_leaves`, ordinary shared Integer
  scope collectors, `assumptions::collect_shared_machine_memory_loads`, and
  `proof/facts/selected_atoms` select shared syntax/read/conversion leaves.
  Their native fallback requires an actually native operand. This classification
  includes the pointer-index edges closed in R7. Existing cold-DAG, growing-prefix,
  binder and registry tests remain applicable.
- `proof/signed_arithmetic/atom_keys` works on shared syntax and retains its
  explicit conversion/opaque refusals. `proof/integer_arithmetic` keeps machine
  observations as shared atoms; no new boxed checker dependency was found in
  these audited adapters.
- Shared `IntegerTerm::RangeFold` bodies and endpoints retain their shared
  walkers on the supported path. Opaque source and replacement handling is covered by the closed R1/R2 paths,
  not an independent unspecified “fold-output” task. `TermRewrite::bits` may
  materialize a replacement for an existing native `MachineTerm`/`CValue` output,
  including a native machine-fold body. That output-family migration belongs to
  steps 2–3; it does not justify R5's export into an already-shared offset field.
- `NativeComparisonView::integer_condition` retains observations; its
  `boxed_value` call applies only to a written operand or literal. The boxed
  comparison wrappers still serve native-input converse readings, Surface
  spelling/planning (`observed_native_surface_comparison` and premise spelling
  in `surface/proof/smart_closures.rs`), and `ProofObligation::verification_condition`
  production through `canonical_observation_form`. The latter also serves the
  frontend's `verify_kernel_standard_theorem_axiom` declaration check in
  `surface/proof/pure_theorems.rs`; it is not merely a printer. Keep these
  frontend/production/output boundaries classified for steps 2/4;
  the removed condition-dispatcher export must not return.
- `eval::canonicalized_offset_index_term` receives an owned native term at a
  producer boundary. `identity::boxed_machine_operation_of_integer_value` and
  `native_comparison_through_integer_operations` are test-only references.
- `resource_tracker::{reads_of_proposition,reads_any_resource,version_mismatch}`
  reach the old Integer read collector from diagnostic history/rendering,
  including diagnostic capture in Surface's proof object. The missing-fold-guard
  helper is `surface/proof/proof_object/resource_steps.rs::describe_missing_fold_guards`.
  These are output/diagnostic callers, not evidence for checking a claim.
- `IntegerTerm::max_variable` still has no in-repository callers. It is public;
  its existence alone is not a live checker dependency or proof of external API
  compatibility for deletion.

The initial audit ran 59 syntax/rewrite controls and 13 registry/dependency
controls; the later R1–R7 closure evidence is recorded above. R5/R6 validation
passed 1,404 scaling/focused tests and the full gate: 7,729 unit/API tests,
58 example projects and 5,123 mdtests. The gate exited successfully in 10m48s
with its existing ten-minute budget warning; no limits were changed.

**Delivery order:** finish the live checker routes found by the cleanup audit
and remove the implicit adapters. Producer increments may proceed when their
own shared construction/obligation paths have zero-export and growth controls;
this does not close unrelated pointer/address checker routes. Keep
one coherent PR open at a time. R1/R2 reuse the exact native-leaf boundary
introduced for tagged addresses; no opaque term-family redesign was required.

### 2. Finish expression producers

`kernel/spec/shared_machine.rs` constructs complete same-format trees of signed
and unsigned addition, subtraction and multiplication. One iterative selection
pass rejects deferred/mixed trees before imports; one construction pass retains
shared children and signed range obligations in left-to-right evaluation order.
Literal folding remains evaluator-only. The single-operation signed module is
removed. Available machine leaves use the existing retained-machine boundary,
so opaque Boolean, pure-function and binder payloads preserve their observation
identity beneath shared arithmetic. The general term importer is not a substitute
for that machine boundary. `SpecExpressionPath` now retains these results as
`SpecValue::Shared`; native inputs and unmigrated sorts use its explicit native
variant, with conversion only at consumers that still require native payloads.

Validation: the final `scripts/check.sh --no-fail-fast` exited 0: 7,111 unit/API
tests, 58 example projects and 5,146 mdtests passed. This includes cold nested
production at 16, 64 and 256 operations, zero intermediate exports, obligation
order, retained inner overflow, held-resource metadata, opaque machine leaves,
and the unchanged Rust integer-language example. Signed-fixture fact-stability
runs passed before and after with zero entries. The full gate took 13m41s,
including a 3m45s rebuild, and emitted its ten-minute-budget warning. No existing
limits were raised and no nightly suite ran.

- [x] Enable nested signed construction with shared obligation operands. This
  producer's zero-export contract is separate from the residual address/pointer
  boundaries inventoried above.
- [ ] Inventory the remaining deferred/partial operations and C/Rust execution
  producers in the existing evaluator, and migrate those still rebuilding
  shared expressions through legacy trees.
- [ ] Preserve evaluation order, scoped obligations, conversion rules and
  undefined-behavior refusals. Keep positive and negative cases for shifts,
  division/remainder, short-circuit conditions and quantified obligations.

**Done when:** the inventoried expression producers construct common nodes and
retain those nodes in obligations; execution and checking do not repeatedly
export their prefixes. Keep
`forward_conversion_requires_symbolic_argument_definedness` as a negative
control: claim completion must not bypass evaluation obligations.

#### Live producer inventory after checker closure

The next producer/common-raising increment retains division, remainder and
shift domains, gives Integer conditionals common children, and raises migrated
machine/Boolean children directly. Indexed current-local naming preserves
existing loop proofs and diagnostics without exporting shared arithmetic.
Its full gate passed 7,205 unit/integration tests and all four fixture harnesses
in 12m55s, over the ten-minute target; no limits were changed. The production
build passed. Full regular-corpus fact-stability runs before and after both
passed with zero fact-dependent lowerings. Native/shared parity, source-drop
round trips, local-index collision checks and deterministic 16/64/256-node
zero-export regressions cover the new boundaries. Steps 2–4 remain open.

| Producer | Representation boundary still to close |
| --- | --- |
| `spec/shared_machine::prepare` | Same-format available 32/64-bit arithmetic, including division/remainder and shifts, retains common children and debts through `SpecExpressionPath::value`. |
| `spec::evaluate_spec_expression_dispatch` | Deferred same-format 32/64-bit arithmetic, including shifts, and scoped requirement handoffs retain results and debts. Opaque/read operands retain shared surrounding arithmetic through domain construction and Integer observations; a session-local memo maps opaque leaves to the existing numeric observation identity without changing exact producer payloads. Same-format 32/64-bit scalar comparisons retain shared operands. Literal-right add chains evaluate iteratively with retained prefixes, including deferred bases. Same-format casts retain the existing result and debts. Specification let bindings retain shared machine values through a persistent lexical map and iterative binding evaluation, including nested values; native C expressions materialize only the lexical names they explicitly read. Symbolic machine conditional joins retain typed guards and shared arms through checking, observation identity, pointer-index transport and Surface spelling. Mixed/narrow/wide operations, representation-changing casts, folds, pure-call arguments, pointer indices and C execution/API outputs still have explicit native boundaries. |
| `eval/operators` and `eval/operators/spec_arithmetic` | C execution, Rust shifts, conversions, bitwise operations and wide operations construct native `CExpressionOutcome::Value` payloads. Runtime-error branches and logical specification debts have distinct rules. |
| `ProofObligation::verification_condition` | Observation canonicalization now retains shared comparisons instead of exporting their prefixes, preserving polarity and native/shared checking equivalence. |


Result-carrier validation: all 1,442 scaling tests passed; the combined gate's
unit phase passed 7,212 tests. Its fixture phase exposed two deferred-shift
domain regressions (PCG and unsigned wide narrowing). The compatibility
boundaries above preserve the old domain shapes: all 58 examples passed their
rerun, all 18 shared-producer regressions passed, and the final production
fact-stability run passed all 5,188 mdtests with zero differences (the baseline
also had zero). The final boundary fixes were checked by these targeted and
corpus reruns; the combined gate was not rerun afterward. Steps 2–4 remain open.

The deferred-domain/comparison increment removes the opaque-domain and deferred
shift compatibility exclusions. Native observation inputs and shared producers
now agree on numeric identity even after the producer is dropped. Signed claim
recognition, certificate term selection and typed comparison spelling read the
retained comparison view. The bounded tagged-address certificate evaluator
borrows shared operands directly, retaining its payload limits, alignment
requirements, relation-cycle refusal and tag rules. Its explicit source terms
and alignment evidence remain the only inputs; no ambient proof search is added.
Signed interval planning bounds and exports selected operands once for the
existing public certificate payload; its affine evidence matcher reads shared
claims directly. Shared cast raising keeps Surface operands, including state
selectors, instead of forcing them through C fragments. Opaque conditional
operands retain their interval rules and Surface conditional spelling. Resource
body requirement matching recognizes retained comparison directions and exact
stored reads. Guarded-consequent indexing, spelling and rewrite selection read
shared comparisons, preserving explicit guard discharge and indexed candidate
selection. Native/shared comparison transport uses the same selected operand
rules. Proper-conjunct extraction keys native and retained observations alike,
without admitting an independently held fact as a conjunction projection.
Cited-condition rewriting visits opaque payloads and folds resolved conditional
arithmetic; wide word equality retains the signed interpretation of high-bit
literals. Difference-graph interval queries borrow retained opaque leaves and
preserve their native branch rules without exporting surrounding arithmetic.
Theorem requirement selection and checking bridge listed equality and disequality
premises as well as order claims. Goal completion checks the selected theorem's
conclusions through the same bridge. General rewrite/transport candidate matching
keeps its existing order-only admission. Resource match/unfold consumers use the
producer's paired clause records directly instead of rechecking them against a
differently represented fact store.
The public signed certificate's selected term payload is still native, as are
the remaining producer families listed above. Steps 2–4 remain open.

Validation after integrating upstream through #2607: all 1,453 scaling tests
passed. The gate's unit/API phase passed 7,242 of 7,243 tests; the one expansion
failure exposed early completion of a mirrored order goal. Restricting the new
completion bridge to equality fixed it, and all 106 selected tests passed on
rerun, including the complete expansion suite and mutex-parity fixtures. All
58 examples passed afterward. The production build and all 5,210 regular
fixtures passed, with zero fact-stability differences (305 seconds). The two
new upstream store-search diagnostic fixtures also passed with retained typed
spellings, including the heap variant outside the regular corpus. The combined
gate was not rerun after the fix; the nightly suite was not run.

### 3. Finish existing term families without redesigning their semantics

`KernelTermNode::Legacy` and `LegacyBool` are explicitly temporary bridges.
`MemoryLoad` still has a native `Pointer` address payload. These require an
explicit representation disposition, not an assumption that a wrapper alone
finishes the split.

- [ ] Enumerate the existing legacy import/export arms and their live producers
  and consumers. Cover Boolean conditions, algebraic values, binders/folds,
  read addresses and complete pointer values already supported at the baseline.
- [ ] Give remaining expression payloads typed common nodes/operand views,
  preserving all existing identity and metadata; remove their generic legacy
  bridges and duplicate expression storage as their consumers migrate.
- [ ] Distinguish expression children from legitimate opaque semantic atoms,
  such as a memory state identity or execution event identity. Such atoms may
  remain opaque; an opaque wrapper around an expression tree is not a substitute
  for migrating its children.

**Done when:** existing term families use the common representation, with exact
construction/import/raise/lower tests and no generic legacy expression bridge
on their live paths. Existing typed APIs may remain as views of the common DAG;
independent parallel expression trees may not.

Preserving the current complete `CPointerValue` payload is in scope. Designing a
new public `CPointer` constructor, changing its fields or changing C provenance
semantics is not a prerequisite. Do not declare issue #2179 resolved by this
representation work. Frontend ASTs and statement evaluators may remain distinct
because they represent source/evaluation information, not a second kernel term
model; states and resources need not become expression nodes.

#### Live payload and common-boundary inventory

| Family | Current storage / bridge and disposition |
| --- | --- |
| Mathematical Integer | `SharedIntegerNode` retains `IntegerTerm` plus a cached `KernelTerm`. Arithmetic, calls and conditionals have common children. Folds and algebraic matches still need typed common children and binder metadata. Remove the parallel native node storage after its readers migrate. |
| Machine values | `MachineTerm` and native `CValue` payloads remain producer/result carriers. Shared arithmetic, casts, machine conditionals and read descriptors are common nodes; fold, application, algebraic-match, pointer-address and floating payloads still use generic bridges on some routes. |
| Logical Bool | Comparisons, calls, equality and conditionals have common nodes. `LegacyBool` still carries pointer/offset/complete-pointer comparisons, algebraic equality, overflow and floating conditions, and Boolean loads. |
| Complete pointers and read addresses | Keep address, designation, opaque extent, qualifiers, subobject extent and access/evidence metadata. Expression children must migrate; state, allocation and execution-event identities may remain semantic atoms. A wrapper around the existing complete pointer tree is not closure. |
| Algebraic values and array references | `KernelTermImport::argument` still uses the generic legacy argument boundary. Constructors, matches and scalar children need typed common nodes; array-reference state identity remains an atom. |
| Raising/lowering | `raise_kernel_term` visits common arithmetic, casts, observations, machine/Integer conditionals and Boolean children directly. Shared arithmetic uses the existing local-name index before expanding children; it preserves current-local spelling without exporting the query or scanning unrelated locals. Legacy payload dispatch, native fact/goal synthesis, certificate-only lowering and the general evaluator-backed lowering path remain distinct boundaries until consolidated. |

### 4. Close the common boundary and declare the split complete

- [ ] Route supported common nodes through shared structural lowering and
  raising. Remove exports to the old speller and duplicate family-specific
  expression conversion paths.
- [ ] Make fact/goal term operands use that common path while preserving their
  proposition, binder and resource structure. A separate fact renderer may
  still have a tracked defect; it must not require another expression model.
- [ ] Delete obsolete bridges and duplicate storage. A compatibility *name*
  such as `ContractExpression = SurfaceTerm` may remain if it denotes the same
  type and carries no alternative behavior; renaming every caller is not a
  completion requirement.
- [ ] Run the final validation below, publish the closed boundary inventory,
  and explicitly mark this representation milestone complete.

**Split complete when all four steps are closed:** common term-level round trips
are exact, checker and producer paths use the common representation, obsolete
expression bridges are removed, and the integration gate passes. The remaining
spellability work below does not silently extend this finish line.

## Final validation and scope control

Retain exact raise/print/parse/lower tests for the existing common term families,
including casts, nested arithmetic, binders, reads and complete pointer payloads.
Test actual obligation discharge and refusal, successful and unsuccessful
checker decisions, historical identities and branch isolation. Run deterministic
scaling tests across growing DAGs, changed contexts and unrelated facts.

Use `scripts/check.sh` as the integration gate; do not substitute a nightly run,
raise limits or weaken proofs. Run the regular-corpus fact-stability audit with
zero differences and record a separate spellability census with its remaining
misses. A globally empty census is **not** required to close this split.

A new census finding blocks the migration only if a reproduction demonstrates
that it breaks one of the closure criteria above: common representation,
term-level round-trip identity, rule parity or scaling. Name that exact route and
test. A failure in existing fact-to-expression synthesis is not automatically
proof that another term-family migration is needed. New regressions introduced
by the migration still need fixing; separating milestones does not excuse them
or authorize placeholders, spelling searches or fact-dependent lowering.

The tagged-address consumer now retains shared operands, including mixed residual
tags containing an explicit native opaque input. Those inputs use the existing
`KernelTerm::Legacy` boundary with a producer identity that preserves their exact
payload; this does not migrate opaque pointer expression families in step 3.
`wide_observation_keeps_tagged_address_equality_rules` proves that with
`x == address(p) + 1`, the checker still refutes `x == x + 1` without a machine
export, and preserves the negated result, source withdrawal and branch isolation.
Tag-form memoization is scoped to the fact/read generation, decision mode and
nesting depth; cached answers retain their source evidence. Multi-size growing
DAG tests cover repeated misses and reuse of checked prefixes.

The R1–R7 reproductions above are closed, but the compiler-assisted cleanup
audit found additional live routes. Finish those checker migrations and remove
the implicit adapters before proceeding through steps 2–4. Do not resume the
census backlog as the default next task.

## Spellability follow-up — outside the split's finish line

Keep these visible without reopening completed migration steps:

- The focused volatile census reports a smart-step `PointerValueEqual` miss in
  `update_pointer_cell.contract`, rendered `replacement == cell[0]`. The fixture
  verifies. Raising currently selects expressions from the underlying pointers;
  the exact original-versus-relowered field mismatch has not yet been isolated.
  Investigate it as a fact-spelling defect unless it demonstrates a closure
  blocker under the rule above. Do not assume it requires a new CPointer design.
- The earlier `design/charon-trial/held-values` census reported `unfold`
  equations with a `match` right side and a call precondition instance recorded
  before its result. Reproduce before claiming they remain current; preserve
  `charon_held_value_locals_are_spelled_by_name` coverage.
- Other introduced-value names, missing fact syntax, total fact/goal spelling
  and a globally zero-miss census remain the broader unspellable-facts project.
  They are not extra unchecked steps in the representation milestone.

Latest landed evidence (#2492, before this documentation revision): the full
gate passed 7,663 unit/API tests, 58 examples and 5,107 Markdown fixtures. Both
regular corpora passed fact-stability auditing with zero differences. The
focused volatile census passed 11 fixtures and reported the one miss above.
These are scoped measurements, not evidence that the split is already complete.

## Delivery and history

Land coherent tested slices in small PRs, one open PR per thread, with auto-merge
enabled. Check queue state before updating a head and verify pushed work reached
upstream after merging. Each PR should identify the checklist boundary it closes
and remove stale active entries instead of appending another chronological
progress narrative. Ask for semantic decisions, not routine ordering.

The [pre-revision roadmap](https://github.com/clicklang/click/blob/93c5fe74cd6ff161782b65a9709ffe57cd3eca76/roadmap/unspellable-facts.md)
preserves detailed consumer migrations, tests, constraints and checkpoint PRs.
The [older handoff](https://github.com/clicklang/click/blob/1e4e07c98fb5354cf6a14ce985c08d5af95f286c/roadmap/unspellable-facts.md)
preserves the original pointer-read WIP, semantic decisions and dropped trials.
Neither historical checklist is the active work queue.
