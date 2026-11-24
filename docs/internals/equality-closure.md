# Equality closure design

This is the design record for the kernel's equality closure: the persistent
graph of pointer, offset, and integer equalities that memory and resource
reasoning query.

The trusted persistent graph maintains affine pointer classes, offset and
int32 congruence, and registered same-state pointer, four-byte scalar, and
complete eight-byte scalar loads. Normalization, transport, memory,
resource-value, range, and resource-lookup consumers query it. Ordinary C
pointer loads keep a storage-relative representation. Wider theories mentioned
here are not implemented and have no current acceptance criteria.

Fact contexts only grow and fork: a branch retains its parent context and
extends a persistent clone, and nothing withdraws a fact. Negative controls
check that a result depends on its support by querying the context built
without the premise, usually the parent. Opposite assumptions record `false` without
replacing the original condition
or deleting its equality support. Explicit context restriction remains separate
from branch backtracking and subject to the checking cost contract.

## Pointer comparison evidence

Symbolic pointer equality and disequality retain both complete addresses,
including a syntactically common block and symbolic reflexive comparisons.
A pointer read from memory (`AddressBase::Load`) names an unknown address, so equal
displacements in its block are symbolic reflexive comparisons as well; unequal
constant displacements still fold to false. Other constant comparisons fold. Keeping symbolic comparisons preserves the
fact lookup used by explicit `close()` after resolving a stored pointer;
reflexivity remains available to normalization and equality closure.
When registering a same-block comparison, the graph identifies its condition
node with the comparison of the two offsets. This is a definitional view of
one predicate, not an additional premise. Later pointer aliases can therefore
reuse the original address comparison without reconstructing a cancelled
base from an arbitrary class representative.

A consumer that accepts an offset equality reads a same-block pointer
equality through `ConditionTerm::pointer_offset_sides`, not by matching
`AddressOffsetEqual` alone. In particular, a `have` at an execution frontier
whose goal compares two loads of one pointer-valued field takes the
load-equality bridge in either form
(`mdtests/loop_node_link_frames_across_parent_link_store.md`).

Retained load-address congruence uses the same view. For an exact same-base
pointer comparison, it selects the source through the existing scalar-evidence
adjacency index and retains that original pointer premise. The full offset
sides must match; coordinate keys only nominate candidates. This avoids
repeatedly proving restricted subsets of a connected component merely to
rediscover the address alias, and a context without the named premise does
not check the derivation. The scaling control
`solve_retains_common_base_pointer_equality_for_load_congruence` covers a field
displacement and increasing connected aliases.

The bridge registers only the selected addresses and offsets. It neither
enumerates pointer aliases nor derives equal blocks from equal offsets.
Truth remains scoped to its admitted premise; a context without either that
premise or the required pointer alias does not hold the conclusion. The
`pointer_comparison_preserves_base_evidence_through_aliases_and_scopes` and
`pointer_comparison_evidence_work_ignores_unrelated_facts` regressions cover
registration order, early queries, missing premises, and ambient scaling.

A full pointer-value query also registers its two numeric addresses against
the current affine block representatives before checking value congruence.
Earlier address nodes may predate a block alias; without these bridges, the
query can miss an established equality depending on premise admission order.
Provenance and retained bounds remain separate value operands: refreshing
addresses does not establish either identity. The cursor-chain regressions in
`src/kernel/equality_graph/fact_congruence_tests.rs` combine symbolic loop
values, a native argument, signed prefix counts and native lengths, with
missing-premise, displacement and address-only controls. Its scaling test
keeps query work bounded while unrelated conditions grow.

Conditional normalization admits cited conditions and their mirrored forms in
source order while retaining an indexed map for condition lookup. Bounded
pointer closure can retain different coordinates after a block merge; a hash
table's iteration order must not choose whether an emitted certificate checks.

## Read-only pointer domains

`PureFactContext::pointer_domain` returns `Unknown`, `Root`, or a selected
subobject bounds without changing the pointer value. Intrinsic bounds are
read directly. An opaque domain uses its retained origin to find an already
registered bounds node and the cached witness of its equality class. The query
registers no terms or reads, runs no closure, and recovers no memory history.
Complete-pointer equality supplies domain knowledge; integer address equality
and equality of widened byte views do not supply the original domain.

Access matching checks the requested bytes or clause range against the cached
selected domain and checks the supplier's object identity. A broader holding
can supply those bytes, including when adjacent holdings were coalesced. When
the required pointer's domain is opaque and has no cached selection, coverage
evidence for that domain that contains the requested bytes, or both clause
endpoints, bounds the access instead; the holding must still have the same
provenance and supply the bytes.
Both clause endpoints are checked in their original 32-bit or native-width
coordinates. The supplier must separately cover the access and provide the
required permission, initialization, and liveness.
Arithmetic formation, member selection, read/write bounds, and clause ranges
consult the same query. Access bounds reuse the context already prepared for
ownership checking, including unresolved opaque-domain misses. Formation and
member selection prepare an expression's fact delta only for an unresolved
domain. Execution retains the original pointer's address,
provenance and opaque domain; copying, local reads, nonvolatile loads and
integer restoration do not adopt another value's metadata from facts.
Explicit member selection and conversions still construct their own structural
views. Complete stored-value equations remain the source of bounds knowledge;
unknown domains still need the existing coverage and resource checks.

The domain unit tests and deterministic scaling tests in
`assumptions/pointer_domains.rs` cover cold queries after late equality
admission, growing related aliases and unrelated facts, branch isolation,
full-width bounds, and an unregistered read with growing memory history.

## Checked object-type evidence

Admitted equations, predicates, and true model-equality conditions retain the
checked object classes on direct pointer values and constructor payloads. The graph indexes those
sources under `(address class, object class)`, using the same supported-fact
buckets as pointer predicates and callback witnesses. A late address merge
moves the support with the class; type lookup reads one selected bucket.
Matching a typed model identity and proving `p == identity` therefore lets a
model constructor or typed helper use `p` without repeating a type argument.
This supplies no ownership or read permission.

Query registration does not admit type evidence. Opaque call arguments can
retain annotations from another interning context and are never used as type
support. Alternative arms, binder bodies, states, weak C declaration
metadata, and destination casts do not
supply positive support. Branches fork the persistent index. Condition and
proposition sources have separate indexes so
clearing one partition does not scan the other. The regressions live in
`src/kernel/equality_graph/object_type_tests.rs`, with deterministic scaling
controls beside the other graph scaling tests.

## Typed algebraic model values

Checked equalities of algebraic model values enter the same persistent term
classes as pointer and machine equalities. Both logical equality propositions
and true algebraic equality conditions admit edges. Direct closure and
semantic fact lookup can therefore combine a checked tactic postcondition
`new.model == old.model` with a match-arm fact `new.model == Empty` to establish
`old.model == Empty`, without repeating the postcondition in source.

Resource arm selection consumes these same classes when it needs the actual
constructor and payloads, including `child.model == context == outer.model`
when a match selects `outer.model`. Each typed class retains one exact root
constructor from an admitted equality. A union carries that witness with the
class in constant local work; lookup visits only the selected expression and
class. The witness shares its immutable payload across class forks and is
rebuilt from the selected equality inputs on restriction. Retaining only root
operands avoids copying every nested constructor subtree during registration.
The matched-resource regression is
`mdtests/resource_unfold_uses_transitive_model_constructor.md`; its missing-link
counterpart rejects selection from another class.

Variables retain their resolved datatype. Constructor signatures retain that
type, the constructor name, arity, and ordered payload classes. Pure calls
retain their function identity, result type, and ordered typed arguments.
A late model or scalar merge propagates through the existing parent-use index,
including machine-valued pure calls with model arguments. Binder-bearing match
expressions remain opaque. This supplies congruence, not unfolding, arithmetic
solving, function injectivity, or new read permission.

Constructors are injective and pairwise distinct, and the closure applies both
rules to classes rather than to stated equalities. Each class retains one
interned constructor application, from any registration. When two classes
merge and both have one, the same variant joins their fields position by
position, and a field wrapped in one argument tag also joins the wrapped
values; distinct variants set the graph's conflict flag, so the context is
impossible. A union reads only its two witnesses, so the work is the arity of
one constructor. `x == Full(a)` and `Full(b) == x` therefore give `a == b`
without a stated `Full(a) == Full(b)`, including nested fields; `x == Empty`
instead refutes the context. Cyclic equations such as `x == Cons(k, x)` are
not refuted: there is no occurs check. Regressions:
`mdtests/constructor_injectivity_through_an_equal_value.md`,
`constructor_disjointness_through_an_equal_value.md`,
`constructor_injectivity_keeps_field_positions.md`, and
`constructor_injectivity_needs_one_value.md`.

Registration traverses only the selected expression, iteratively. Hot node and
support keys are shallow IDs. Resolved root schemas are interned once per
schema allocation and nominal instantiation; retained schema Arcs prevent
allocation-identity reuse. Distinct nominal types, generic arguments, or root
schemas do not share a type token. Exact checked edges are retained for
restriction rebuilding. Branches and restricted contexts use the same
scope rules as the other graph fragments. Restriction constructs the selected
condition graph before filing selected proposition edges; it never rebuilds
inherited scalar edges only to discard them. Clearing a model-free proposition
fragment retains its existing scalar graph.

## Pointer-valued pure-call congruence

Pointer-returning pure calls use the same curried typed application nodes as
other pure calls, with a distinct pointer-result head. Registering a call's
block connects the application to its zero-offset address. Existing pointer
value witnesses carry newly equal results into the affine pointer classes,
just as they do for pointer reads. Displaced addresses and read applications
therefore consume the same result equality.

A call is registered once per block. A shared iterative dependency queue drains
nested pointer calls and scalar reads; a draining guard prevents nested argument
registration from recursively entering the queue. The ordinary parent-use index
propagates late argument aliases without scanning ambient facts. Signatures
retain function identity, argument order and types, and array-reference read
states. Calls grant no ownership or separation, and equal results do not
imply equal arguments. The `pointer_call_tests` unit and scaling modules exercise
late model aliases, nested calls, states, missing premises, and selected work at
multiple input sizes. The surface regression is
`mdtests/pure_pointer_call_congruence.md`.

## Ordinary integer expression congruence

Mathematical `Integer` equalities enter the shared classes. Congruence follows
negation, addition, subtraction, multiplication, truncating quotient/remainder,
typed machine observations, and pure calls. Integer arguments and constructor
fields register those same terms. Thus model equality reaches a C-valued getter,
its `to_integer` observation, an enclosing count expression, and an admitted
Integer comparison without an explicit rewrite.

Machine expressions reuse the common unary/binary operator decomposition.
Integer arithmetic, bitwise operations, shifts, integral conversions, and
`IntegerToMachine` applications retain their operator and carrier width;
conversions also retain source/destination types. Existing specialized addition,
read, and unsigned 64-bit application nodes remain in use. Pure-call arguments
cover `_Bool` and every supported signed/unsigned integer type, including 128-bit
values, with distinct C type tags. Floating-point expressions remain opaque.

A wide shift's independently promoted count has no source-type tag in the term
representation. Its complete count expression remains opaque rather than guessing
a width. Congruence still propagates equalities of the shifted value. Binder-bearing
matches/folds and legacy untyped pure applications also remain opaque.

Integer constructors fold machine literal observations. Registration therefore
connects each selected Integer literal to its representable typed machine
observations, at most ten fixed formats, using checked range conversion. No
truncation or signed/unsigned identification is inferred. This makes a late
machine equality to a literal reach the canonical Integer numeral.

Registration visits only selected expressions; shared Integer DAG nodes are
visited once per registration. Curried applications use the existing indexed
parent-use propagation for late equalities. There is no ambient-fact scan,
function unfolding, cancellation, or arithmetic search. Existing branch,
restriction, and state scope rules apply unchanged. Regressions live in
`integer_tests`, `ordinary_expression_tests`, and their scaling counterparts;
`mdtests/integer_count_model_congruence.md` exercises source-level count lookup.

## Predicate and callback pointer matching

Semantic predicate lookup and callback-contract selection query the same
address-class buckets. A predicate witness is stored by its first pointer
argument and a bounded shape selector; pointer arguments become typed holes
in that selector, while other arguments and memory versions remain. Matching
checks all pointer arguments through equality closure with equal C types and
all other arguments exactly, including the complete C state. This supplies
pointer substitution only, without unfolding or state transport. Exact
membership still controls admission and consulted premises.

The same bucket mechanism indexes nominal callback witnesses by contract name.
Call selection checks the declared contract's exact function signature, as
before. Multiple witnesses of one contract retain their independent sources;
lookup chooses one without scanning older state witnesses. Late address-class
merges move only the affected buckets. Persistent branches share unchanged
indexes, and restriction removes unsupported matches. The regressions
`callback_contract_uses_checked_pointer_equality` and
`callback_call_uses_checked_pointer_equality` cover direct closure and dispatch
through an unchanged C callback table.

## Shared typed pointer reads

A registered typed pointer read is a congruence application of its state
read identity, complete address, and load interpretation. Complete address
classes, rather than only affine block coordinates, determine equality of
these applications. The existing parent-use index propagates late address
merges to the affected reads. Each read-value class retains one typed-read
witness. Merging classes emits equality of the corresponding zero-offset
pointer values into the existing affine class-update stream. Ownership and
range indexes therefore receive the same consequences without rediscovering
read equality or enumerating aliases. The pending stream is persistent so a
context fork cannot copy unrelated deferred work.

This rule establishes values only: it supplies
no read authority, initialization, allocation identity, or cross-state
frame proof. Memory state read identities retain their existing independently
checked representation-only normalization.

Immutable definitions and checked read evidence serve different purposes.
An existing C value can keep its original load definition when a later read
returns it from a cached cell. A checked resource-index evaluation retains
that later state and selected address in its certified producer binding.
After its prerequisites pass, it admits `value == Read(retained_state, address)`
through the graph's existing checked-equality input. It does not mutate the
value's definition or install a global observation. The input is branch-local
and retained by input checkpoints; rebuilding a context without its evidence drops it.
Offset equality queries register the same producer-retained typed-read
definitions as full-pointer queries. Registration visits only the selected
operands; it never infers address-base identity from equal offsets.

A checked pointer store also emits the equation between its complete stored
value and the typed read at the written address in the resulting state.
The equation travels with the certified execution facts into the ordinary
graph, so an equal-address query does not require a preliminary read through
the store's address form. It relates only that state; a subsequent write needs
its own preservation evidence. Scalar or partial stores do not emit pointer
value equations.

When a logical read returns a cached pointer, its path also carries the
producer-derived equation between that value and the current cell's typed
read. A named scalar cache supplies this equation only when its original
producer recorded a complete eight-byte pointer load. The equation enters the
ordinary equality graph with the path facts; the evaluator does not mutate
the caller's context or promote a global observation into proof evidence.
These equations are distinguished from branch conditions: they neither select
a lowering candidate nor add premises to a quantified goal or an execution
theorem. Definedness checks omit them from safety conditions, and checked
branch interfaces keep them local rather than requiring another arm or the
abstract successor to establish them. Pure capture may discard them, and symbolic match arms and range-fold
bodies keep their equations local. Changed cells, missing aliases, restricted
contexts, and narrower scalar reads cannot reuse the old relation. No read
permission is introduced.
A call's postconditions are lowered against the caller's own post-call
state, so their reads are the caller's reads and need no bridge
(`mdtests/a_call_postcondition_cast_is_available_after_the_call.md`).
Diagnostic state histories remain explanatory metadata, never proof evidence.

Compound pointer and offset queries retain the generation at which their read
dependencies were registered. Repeated queries reuse that result; a newly registered logical
read definition changes the generation and invalidates earlier misses. This
cache retains term dependencies only, never a successful equality judgment.

Ordinary and volatile program reads do not use this resource-index admission
path; this admission is not universal read adoption.

## Shared 64-bit expression congruence

`add_uint64_equality` admits checked 64-bit equalities into the same persistent
term classes; `are_uint64_equal` queries their closure. UInt64 addition,
subtraction, multiplication, division, remainder, and bitwise AND/OR/XOR are
congruence applications, with distinct operator tags. Pointer-to-word address
expressions use the complete pointer address class. No cancellation,
injectivity, arithmetic definedness, or memory access permission follows.
Unsupported constructors remain opaque.

Pointer-to-word casts also retain the source pointer's checked object class
when one is known. The annotation is a field of the stored address term, so
memory storage, rewriting and substitution carry it without a global
address-to-class registry. It is not part of the term's identity: equality,
hashing and ordering ignore it, as they ignore a pointer value's class. A
classed and a bare form of one address are therefore one term in equality
closure, exact fact lookup, `rewrite`, `contradiction` and theorem-premise
matching. The supported tag operations carry the
annotation to decoding; an integer-to-pointer cast restores the original
class, never the destination type's class. A bare address remains unclassified,
and unavailable origin evidence cannot supply a class. Loop
object-class joins and incompatible-access checks remain in force.

A `Bits64` read uses its registered defining state and complete address,
with an eight-byte producer-width check for named scalar reads. It is a
separate application sort from pointer reads and int32 values. Equal addresses
at that state therefore produce equal words, and the ordinary parent-use
index propagates that equality through surrounding expressions. Different
states are not unified by this registration; existing checked frame or
copy evidence must establish any cross-state equality.

Exact wide premises are retained as typed edges for context rebuilding. Derived resource indexes receive them through the same
persistent input history. Ordinary condition and required-obligation checking
query this closure, including contexts that defer broader search. In
particular a fold needs no special rule to combine a read-address alias with
another pointer alias nested in a packed parent/color equation.

## Fact availability through congruence

`PureFactContext::contains_known` is the semantic lookup used by proof-fact
availability and the direct check in `close()`. Exact membership remains a separate operation
for premise admission and consulted-premise checks. Lookup first checks
the exact index, then asks the same scoped graph used by equality consumers.
It performs no unfolding or implication search.

Machine equality goals ask for class membership. Supported machine comparison
facts (including false conditions) have typed application signatures annotated with
their admitted truth value. A late operand equality updates those signatures
through the existing parent-use index; queries never scan ambient facts.

Machine-valued Click function applications also have congruence signatures.
Their argument list uses shallow binary application nodes, preserving function
identity, result width, argument order, C types, and array-reference state
identity. Int32, UInt32, UInt64 and pointer arguments use the existing scalar
and complete-address classes. Other arguments, including binder-bearing
algebraic and mathematical Integer expressions, currently retain exact opaque
identity. Legacy applications without argument sorts also remain opaque. This
does not introduce injectivity, arithmetic solving, memory permissions, or
implicit equality between different states.

Condition truth follows scoped persistent graph forks. Its exact support is
retained for rebuilding after replacement or context restriction;
sibling branches cannot import each other's facts or query registrations.
Resource-index checkpoints apply value equalities only: comparison truth does
not invalidate a memory index or extend its admitted-equality history.

## Current interface and trust boundary

`kernel::equality_graph::EqualityGraph` is part of the **trusted kernel**.
Its `add_equality(left, right)` operation admits an equality established in the
current proof context; `are_equal(left, right)` queries the maintained closure.
A negative query means unknown, not disequal. Insertion's return value reports
whether a class merge occurred, not validation of the supplied premise.

Pointer operations keep pointer-typed operands; `add_offset_equality` and
`are_offsets_equal` accept whole address offsets. Supported pointer-load
applications and offset terms register on demand during insertion and queries.
`add_int32_equality` and `are_int32_equal` admit and query explicit int32
equalities, addition congruence, and registered same-state int32 load congruence. The uint64 interface above extends the same closure to wide reads and selected
wide expressions. Further sorts and consumers remain separate work. `pointer_is_classed` and `pointer_spellings` are explicitly
pointer-specific compatibility helpers for legacy consumers.

Every read application (pointer, int32 and uint64) takes the read's
*numeric* address, `UInt64Address(address class)`, as its operand, not the
pointer's address class. Memory is addressed, so two reads of one state at
equal addresses read the same bytes. A C pointer comparison states only a
integer address equality (`program_pointer_comparison_condition`), which merges the
two numeric addresses and so the reads, but never the address classes that
pointer equality and read authority use. Equal pointers still have equal
numeric addresses by congruence. The first read at a displaced address
`AddressShift(base, k)` also defines its numeric address as
`UInt64Address(base) + k`, so integer address equalities of two bases relate reads of
one field of each; an address that is never read, such as a resource's, adds
no numeric nodes. Regressions:
`reads_at_equal_addresses_are_equal_without_equal_pointers`,
`mdtests/pointer_loads_equal_after_late_address_equality.md` and
`mdtests/pointer_field_loads_equal_after_late_address_equality.md`.

Term interning and affine decomposition run under the graph mutex and do not
canonicalize memory or traverse its history. Public scalar and offset equality
queries normalize their selected scalar indices before locking while preserving
the offset expression's addition nodes. A raw scalar read can
receive an exact-state observation name with its recorded kind and access
width; that internal definition introduces no path proposition or read authority.
A different state still needs the existing checked normalization or frame
bridge. `raw_read_address_registration_does_not_walk_memory_history` measures
selected registration beside 0, 16, 64 and 256 unrelated classes. The existing
state/support regression separately checks raw/named equality and premise scope.

Kernel consumers use `PureFactContext::pointers_known_equal(left, right)`
for equality already established by this trusted graph. It neither searches
arithmetic facts nor walks an alias component. `false` means unknown.
`pointers_proven_equal_by_reasoning` names the broader arithmetic/condition
judgment; `pointers_proven_equal_for_memory_resolution` retains structural
object-distinctness and explicit resource-separation guards. A graph answer
alone supplies no memory access authority.

Kernel rules may trust the graph's answers in their own proof context. There
is no `explain` API or separate derivation checker. Expanded proofs can use
simple kernel equality queries; expansion need not print the internal
congruence steps. Such a consumer must preserve the checked premises, branch,
load interpretation, and memory state of the query. Cloning shares
persistent storage while keeping subsequent additions branch-local.

`normalize() using { ... }` queries this existing graph while reducing
pointer and int32 equality conditions, including guards of conditional expressions.
Successful queries replace equality conditions with true; unsuccessful queries
leave them unknown. The same traversal handles equality leaves and nested
conditions. Graph queries may use ambient graph facts; the `using` list
restricts the additional conditions used for reduction. All cited premises must still be available and
supported. Other ambient facts, quantified bodies, and cross-state frame
search remain outside this operation. Expansion retains the simple step and
rechecks it in the same proof context, without an explanation API or a
per-tactic graph rebuild. Restricted `close() using` planning checks a
normalization candidate against only its selected context before emitting the
simple step; omitted ambient equalities do not participate in that search.
Explicit pointer-offset equalities also enter the
same graph and are available to this normalization check. This covers ordinary
C pointer parameters, which lower to offsets in a shared block, without
changing their representation.

The offset fragment interns whole terms with shallow keys and uses persistent
union-find weighted by members and parent uses. Its query first recognizes
exact affine-equivalent byte offsets, including regrouped or reordered sums
without a premise. `close()` uses that query for same-block pointer conditions,
which lower to offset equality. Addition signatures identify operand classes,
so equal operands establish equal sums. Indexed parent uses
propagate late merges through nested additions with an iterative worklist;
parents of the lighter class are revisited. When a class first acquires a
literal value, its existing parents also receive constant evaluation. It preserves widths,
signedness, and machine-term state identity, and adds no arithmetic solver
or cancellation rule. Queries and additions use indexed access. Existing
context restriction rebuilds retain all graph
fragments from their remaining exact equality indexes. The pointer query
compares affine coordinates and whole offset classes inside the graph. Same-block pointer premises also join whole offsets.
Equal-base and representable constant-displacement queries use direct offset
class lookups, including either translated form. At an unclassed ordinary
base with no offset merges, the known-equality query stops after reflexivity;
explicit offset normalization remains available through `are_offsets_equal`.
This avoids normalization work during unrelated field-separation checks.
These checks require no alias enumeration or cancellation rule.

Checked cross-block pointer premises involving the shared external-argument
block, concrete storage, or an unraisable displacement also join their raw
`address(block, offset)` applications. An address class retains one offset
witness per exact block. Merging classes with a shared block joins those
offsets: `address(A, x) == p` and `p == address(A, y)` establish `x == y`,
regardless of the affine representative. This is exact byte-address
injectivity within one block; addresses from different blocks do not imply
equal offsets. Only witnesses in the lighter class move, so unrelated
address classes are never scanned. Offset-class merges then propagate by
ordinary congruence, so `x == y`, `address(A, y) == z`, and `z == null` establish
`address(A, x) == null` in any insertion order. Affine block merges translate
registered applications when that translation is expressible. Query registration
can use a stated `i64::MIN` translation directly without constructing its
opposite sign. Unsupported translations otherwise remain unknown.
Raw applications preserve these exact premises independently of affine
coordinates; derived load merges retain their existing indexed closure
without eagerly duplicating every application.

A selected address with a constant byte displacement also registers a shift
application on its complete base address. Equal base addresses therefore remain
equal after the same displacement, even when an earlier block merge flattened
the base into affine coordinates. Registration publishes one selected prefix;
it does not enumerate aliases or recursively publish every prefix. Each raw
address form retains its registered shift definition, so repeated queries
do not repeat base registration or closure. This supplies integer address equality only: field access still requires an owned range of the correct
width. Regressions cover multiple owned fields, late cursor aliases, different
offsets, missing ownership, and constant query work as unrelated fields grow.

Explicit int32 equalities use typed nodes in the same term-class engine
as offsets. Int32 addition, unsigned division/remainder and bitwise XOR have
operation-tagged application signatures and shallow child IDs; other scalar
operations remain opaque. Equal operands give equal results, including late
equalities and nested applications. Signed division/remainder stay distinct;
unsigned congruence does not establish a nonzero divisor or any other arithmetic
definedness obligation. Registration canonicalizes each
input once before walking its supported constructors. Literal sums use the
kernel bitvector wrapping semantics; equality does not prove C signed
definedness. No commutativity, cancellation, or arithmetic solver is added. The graph preserves canonical machine-term identity, including
memory states. Int32 scaling is a congruent application: equal indices
with the same byte width give equal offsets, and existing offset addition
applications propagate that equality. Parent-use indexes handle late scalar
merges in the same worklist. Literal indices join their folded byte constants
when multiplication fits i64. This does not infer congruence for unsupported scalar operations,
64-bit or mathematical-integer equality, or general injectivity of offset constructors. Exact scalar premises are filed under shallow canonical edge keys. `MemoryLoad`
expressions are not separately interned for support tracking: that would allow
cross-arena state comparisons to traverse unrelated memory.

Checked signed int32 addition-overflow facts use the same predicate classes.
Overflow checking consults this retained truth before reconstructing operand
intervals, including the reversed operand order of this symmetric predicate.
Thus an established `defined(x + z)` follows checked aliases of `x` and `z`;
equality alone never establishes definedness. Branches and states retain
the ordinary typed graph scope, and this predicate does not match subtraction
or a 64-bit overflow condition.

A false checked signed int32 multiplication-overflow fact on `x` and a
constant `K` from two to `INT_MAX`, in either operand order, merges the byte
offset of the product, `Int32Scaled { x * K, 1 }`, with element `x` at stride
`K`, `Int32Scaled { x, K }`. Both sign-extend before scaling, so they differ
only where the `int32` product wraps, which the fact excludes. The rule fires
in either registration order through two maps keyed by the product's shared
kernel term: admission files the product as defined and merges the byte-offset
node if one is already registered; registering a byte-offset node of a
product by a constant files the node and merges it if the product is already
defined. Admission interns nothing when no byte-offset node exists, so an
operand held only in shared form stays unexported
(`retained_overflow_source_lookup_ignores_unrelated_guards`). A defined
product counts as a pending equivalence, so an offset query registers its
offsets rather than answering from representation alone. The work is a
constant-size match and one keyed lookup per admission or registration; no node
or fact is scanned. C
pointer arithmetic over a `char`-width displacement `i * K` records this fact
when the path's facts decide it, since lowering keeps the written byte offset
(`docs/internals/raise-lower-principle.md#lowering-is-fact-stable`). Regressions:
`a_byte_product_joins_its_element_offset_in_either_registration_order`,
`a_byte_product_stays_apart_without_its_no_overflow_fact`, and the scaling
test `a_byte_product_merge_is_keyed_and_ignores_unrelated_products`.

Constant endpoints of checked signed int32 order facts annotate their value
class with an interval. A class union intersects these intervals, so overflow
checking can use bounds supplied on an equal variable or a same-state read.
The annotations are persistent across forks and are rebuilt from the selected
facts after restriction. Strict and complemented comparisons retain their signed
meaning; unsigned and 64-bit comparisons do not contribute. This ranges the
wrapped value only: bounds on an expression's result do not establish that its
own C operation is defined. Lookup follows the class representative rather than
enumerating aliases or deriving pairwise order facts. Multi-size regressions
cover incremental aliases beside unrelated bounds without a fallback fact scan.

True offset premises also feed the shared graph through the existing checked
int32 element-index interpretation: four-byte scaling, aligned constants, and
supported additions. Equal byte offsets then imply equal int32 index residues.
This premise translation files into the same edges as explicit scalar
premises. It does not
infer exact offset equality from equal wrapping residues.

`PureFactContext::int32_values_known_equal(left, right)` is the shared query
for wrapping int32 value equality in the trusted graph. Condition decisions,
transport, resource matching, and memory consumers use the same maintained
closure, including addition, literal evaluation, and registered load
congruence. Queries do not build the legacy condition-fact index; deterministic
regressions check bounded cold query work beside increasing equality classes
and unrelated facts, as well as late merges and persistent branch isolation.
Opaque operands use existing-node lookups. An absent nonliteral opaque
endpoint cannot be produced by constructor registration, so such a miss stops
without interning unrelated applications. Supported additions and registered
loads still register when congruence or literal evaluation can establish equality.
Representative lookups use a disposable node-ID cache guarded by the merge
history's epoch. Unions invalidate entries lazily; forks start an empty local
cache in constant work, while semantic graph storage remains persistent.
There is at most one cached representative per node, with no term-pair cache
or deep structural key.

Residue equality remains distinct from exact byte-offset equality. Memory
resolution checks that both rebuilt indices are exact before a positive
residue equality can prove an offset equality; unequal residues can still
refute one. `wrapped_index_sum_does_not_decide_pointer_offsets_equal` and
direct memory-resolution regressions protect this boundary across element
widths. Resolved-load value comparisons require a recorded four-byte read;
a byte, short, or wide read cannot acquire int32 semantics by resolving its
stored term. A certified store equation for a four-byte word records that
width at its cell before naming the read, as a typed load producer does. The graph then
registers that read as a word read when the step admits the equation. A
context that admitted it under the unrecorded fallback width would never
revisit it after a later typed read of the cell, and would know less than one
rebuilt from the same facts
(`a_store_equation_admitted_before_a_typed_read_joins_reads_at_equal_indexes`). The general memory and expression reasoning APIs still perform
their explicit checked judgments; the known-value query does no arithmetic
search or state transport.

The lazy exact-equality index remains for consumers that enumerate aliases or
produce premise-path evidence. Those are distinct operations, not a second
Boolean equality checker.

Wide-read alias checks retain the latest producer observation for each load
identity in the current function epoch. Assigning a load identity, including a
cache hit, records its complete live state and address. Two model match arms
can reuse one identity while their live histories are
unconnected; the selected check tries these observations before its original
origin-based rule. Both routes retain the eight-byte kind and check pointer
aliases and intervening effects. The observation creates no read authority and
never changes the identity's defining equation. Lookup touches only the selected
identities, with one retained observation per identity and epoch. Session capture and
restore share its persistent map root; scope, changed-word, width, cache-hit, and
16/64/256/1024 unrelated-observation regressions cover it.

Resource body checks use the retained 64-bit adjacency index when a copied
word receives a different read name. They query only the stated equation's
endpoints and captured variables, apply the existing checked equality rewrite,
and require the rewritten body fact in the original context. This covers a word
that recurs inside its packed parent address or color mask. It assumes no proposed
body fact, creates no memory authority, and does not promote a 32-bit equality to
a 64-bit one. The regression measures the same query beside 16, 64, 256, and 1024
unrelated equalities and checks missing, out-of-scope, and narrow aliases.

The central memory resolver asks pointer classes for cross-block equality
and offset classes for exact same-block byte-offset equality. Its pointer
query still rejects structurally distinct blocks and explicitly separated
ranges; its offset query still treats equal wrapping int32 residues as
insufficient unless the existing exact-index rebuild check succeeds. A graph
offset edge can flow
through int32 scaling and offset addition into a pointer address without
building the legacy scalar fact index. Context forks and
restriction keep these answers scoped to their supporting premises. Broader
memory arithmetic and framing rules remain in the resolver.

The simple pointer-equality decision uses typed graph queries only; it does
not scan ambient condition facts or walk an alias component. Overflow-guarded translation such as
`p == arr + i` after incrementing `p` and `i` instead uses an explicit
`close() using` proof with the entry pointer relation and strict index
bound. A displaced cross-block query uses an exact translated offset edge
only for a representable constant base displacement. Symbolic displacements
can remain unknown until a checked proof supplies the translated equality.

The memory-separation reader uses the same known-equality query. Exact alias indexes
remain for evidence-producing enumeration and other consumers; their presence
does not imply a second Boolean pointer-equality system. Deterministic tests
cover mixed offset/block chains, all premise insertion orders, late offset
merges, branch isolation, and bounded query work beside growing offset classes.

The full and shallow `int32` equality decisions use the shared known-value
query. Explicit negative premises, arithmetic rules, and checked memory
resolution remain separate. Int32 fact transport uses the same query before
its structural and broader expression rules; it has no separate Boolean
fact-path fallback. Exact pointer-offset decisions retain their no-wrap guard.

The commutative int32-addition matcher also queries the graph when comparing
individual addends. A reordered sum can therefore use registered load
congruence or a joined scalar class even though the graph does not itself
reorder addition. Other checked addend rules still cover forms outside this graph fragment.

Direct memory-resource matching queries graph equality for its int32 range
start and end values through the shared known-value query. These fields are
scalar values, not byte-offset equivalences; the resource base still follows
its separate pointer check. Congruent sums and registered same-state loads
can therefore identify equal range endpoints, while changed states and
missing premises remain distinct.

The checked `ProgramValue::Int32` value comparison queries the graph before its
broader memory-resolution path. Direct composite, token, and instance matching
use that shared typed rule for resource arguments and instance fields, rather
than maintaining a resource-specific graph check. Byte-typed values and pointer
arguments retain their separate rules. Registered loads in one state may
match as values, while changed states and missing premises do not.
Multi-size regressions check that graph matches avoid building the legacy fact
index.

Contract certification's `int32` equality check uses this typed int32
value rule after its checked cross-state load rule. Graph-congruent sums and
same-state loads therefore certify without searching the legacy fact index;
changed states and missing premises still fail. This affects scalar
equality claims, not pointer-offset certification.

Certification of call- and loop-havoc mutable-range lists uses the typed
int32 value rule for each start and end, after separate width and pointer-base
checks. The general range-endpoint helper also serves scaled pointer offsets;
it has not been changed to accept wrapping graph equality as exact address
equality. Regressions cover same-state loads, changed states, missing
premises, width mismatch, and multi-size queries without the legacy fact index.

The structural, memory-resolution, and covering-span loadable-range readers
share one typed int32 value rule for matching byte spans at the same
base. Their callers retain the range-availability check for the goal state;
equal spans do not supply viewability by themselves. Tests retain the
loadable-premise and base boundaries and check direct multi-size queries
without the legacy fact index.

Same-base range containment uses the typed int32 value rule when its
signed endpoint-order check has equal operands. Equal endpoint bitpatterns
establish `<=`; this does not infer an exact byte-offset difference from a
wrapping scalar equality. Other order and containment rules remain separate.

When a signed-order fact is found by one exact endpoint, its other int32
endpoint is compared through the graph first. The containment order check
tries these indexed facts before its broader scalar equality fallback, so a
graph-congruent match does not build the legacy fact-path index. Candidate
lookup still requires one syntactic or canonical endpoint key; it does not
search every order fact for a graph-equivalent endpoint.

The kernel comparison of condition facts for certified transport uses the
typed int32 value rule for operands of matching signed-order or equality
conditions. Condition kind and truth value must still match. Registered loads
remain scoped to their defining state, and a context without the premise
lacks its consequences. Multi-size queries avoid the legacy fact index.

Allocation continuity across a call compares its two 32-bit size values
through the typed graph rule after the separate allocation-base check. This
does not use wrapping value equality to establish pointer-base equality.
Regressions cover same-state loads, overwrite and missing-premise boundaries,
different bases, and multi-size graph queries without the legacy fact index.

After indexed resource matching misses, the zero-ownership fallback uses
the typed int32 graph rule for the required quantity. This is value equality
with zero, not a resource-key or pointer match. Regressions cover graph-
congruent registered loads, changed states, missing premises, and
multi-size zero-quantity queries without the legacy fact index.

For a range pair already selected for composition, endpoint comparison uses
the graph-backed int32 condition decision. The composition helper does not
repeat a separate legacy fact-path walk after that decision. Candidate
selection remains its own index boundary: normalization does not yet discover
every pair whose endpoints become equal only through graph congruence.

After the existing memory resolver establishes a four-byte scalar load's
value, load equality compares it through the shared int32 query. Resolution still supplies the value in the
load's state; graph equality neither resolves stores nor grants read or
frame permission. Other load widths keep their existing comparison path.
Regressions cover both comparison directions, a changed state, missing
premises, a one-byte load, and multi-size query work.

When both operands are resolved four-byte loads, the same path compares their
checked stored values through the same graph query. Neither load's opaque name needs to equal the other load's stored term.
Each value still comes from its own recorded state. Changed or missing
evidence and a resolved one-byte read do not use this two-load rule.

Registered four-byte scalar loads also participate as int32 applications. Their
signature contains the registered defining state's read identity and the
complete address class, as pointer and uint64 reads do. A checked address
equality therefore gives equal reads at that state, even when its block
relation has no affine form. Late address merges propagate through the
same parent-use index as addition and scaling.

Registering an 8-, 16-, 32-, or 64-bit integer read does not equate it
with a value recovered from the memory cell cache. Native and shared raw
read inputs for these widths use read identity selection rather than
cached-value canonicalization at this graph boundary. A producer's retained
store equation supplies the value equality; ordinary congruence then
propagates it through address aliases and enclosing expressions. The equation
remains scoped to its fact context. Signed-byte reinterpretation and exact
projection links still relate read identities without fetching cached values.
Scalar registration no longer retains an observation-origin memory for a
cached-cell lookup. Function-pointer stores also retain an explicit typed
read equation. Read registration has no pending cached-cell lookup queue,
unresolved-cell retry index, or mirrored alias-class maps. Separate checked
pointer-read authorities, memory-resolution APIs, and other callers of
compound-term canonicalization remain outside this registration boundary.

Compound machine-expression inputs to the graph select read identities while
retaining their operators; preparation does not run `canonical_term` to
substitute cached values into them. Already-selected reads retain their exact
identity. Read applications and explicit equations connect `read + 3` to `10` after
`read == 7` is admitted, without importing that equality into a sibling context.
The `compound_read_queries_require_explicit_equations` regression covers native
32-/64-bit inputs, shared 32-bit inputs, and late address aliases. The scaling
regression `compound_read_query_ignores_cached_expression_size` keeps the query
fixed while growing a cached expression that it must never inspect. Raw read
kinds outside the migrated integer widths retain their existing preparation.

Cold scalar queries use address congruence and explicit equations instead of
enumerating an address class to find a cached cell. Scaling tests cover growing
alias classes and unrelated cells at each migrated width.

Selected int32 operands prepare their pointer dependencies before registering
the scalar read. A shifted raw pointer read imports only the exact definition
retained by its typed producer; matching arithmetic without that metadata is
not a pointer read. These operations inspect the selected expression and new
parent uses, without scanning unrelated definitions or address forms.

The defining state can already be an assumption-free canonical projection.
The graph uses that registered definition, never the mutable live origin. It
does not infer a new address relationship or equate distinct defining states,
search for frame evidence, resolve stores, or grant read permission. Unregistered, unknown-width,
and other-width loads remain opaque. Existing canonicalization can independently
retain a value across a justified memory change; this slice adds no new rule
for doing so. Global load naming remains independent of contextual equality.

Checked transport conclusions enter the ordinary int32 equality interface.
For example, after a store to `p[k]`, explicit transport can use `i != k` to
prove that `p[i]` equals its entry value. Rewriting the current index with
`i == j` lets `close()` close the corresponding goal for `p[j]`.
[The executable composition example](https://github.com/clicklang/click/blob/master/mdtests/transported_int32_load_congruence.md)
shows the separation, transport, and rewrite steps. Regression tests remove either
premise or the bridge, reject an overlapping store, recheck expansion, and
verify that a context without the bridge lacks only its cross-state consequences.

## Scope

A proved equality must have the same meaning at every kernel consumer. The
kernel keeps one persistent equality service using congruence closure without
saturation. Hypotheses, checked proof steps, and execution contribute
equalities; congruence propagates them through registered applications. The
service does not invent rewrite rules or search arithmetic identities.
Ordering, general arithmetic, and cross-state frame derivation remain
outside the closure; a checked theorem from one of those procedures can
contribute an equality to it.

## Semantic boundaries

### Stable names, contextual equality

Term IDs identify assumption-free syntax or an established assumption-free
canonical form. Hash-cons nodes using stable child IDs, sorts, and operator
payloads rather than repeatedly comparing deep terms. Global load naming
cannot use one proof path's equalities: the registry is shared across paths.
Two names may be distinct while their values are equal in a particular path.

Union-find state, application signatures, parent-use lists, derived class
attributes, and equality-sensitive resource indexes belong to the persistent
path context. Forking shares the prefix; adding an equality to a branch must
not change its parent or sibling. Adding equalities must never invalidate a
previous equality answer.

### Pointer values and address offsets

A typed pointer-load application in the equality graph denotes the stored
value independently of the storage address form and pointee width. The
graph can answer equality of two such applications without replacing the
`Address` values produced by C execution. A live caller must supply the actual
defining state and address from a typed load site or checked evidence. A
loaded value is represented only by its `AddressBase::Load` base; an address indexed
by a loaded scalar (`a[*p]`) is pointer arithmetic, never a read.

The bridge from a completed nonvolatile C pointer read to the graph
application is execution evidence scoped to that path. The typed producer
registers its value with the exact defining state and address; only a
matching defining equation in the path's fact context files the equality in
the graph. It is not published as an ordinary proposition premise: doing so
changes a statement theorem from `Executes` to `bridge => Executes` and makes
resource child-argument checking reject previously readable expressions. The
graph relation changes neither logical premises nor read permission. Volatile
reads do not register this bridge.

Specification pointer loads retain an exact definition supplied by their
typed producer as graph term metadata. Resource-entry cells and lazy cell
ranges use the same typed constructor and retain this definition before any C
access, so a later read through a model alias has the same identity even at a
nonzero field offset. These definitions are shared across
contexts within one verification session, like load-variable interning;
address hypotheses, unions, and their consequences remain in persistent
path-local graph roots. Reconstructing a context must not forget what a logical
term denotes. Registration never decodes arbitrary pointer arithmetic and adds
no proposition premise, ownership, read validity, or cross-state equality.
Each query registers only its named values and their recorded dependencies.
Filing a checked pointer equality also registers the producer definitions of
its two operands. A later query can therefore use a read hidden behind another
class member without first comparing that read directly or searching the
class for read forms.
A registration generation distinguishes reasoning memo entries from earlier
misses, without scanning or rebuilding the proof environment. `close()` can emit
`normalize() using {}` to check an equality against this ambient graph.
The nonrecursive `mdtests/egraph_resource_pointer_load_alias.md` regression
checks this after an unfold publishes integer address equality.

An explicit pointer rewrite uses this producer metadata to distinguish a
pointer-valued read from ordinary address arithmetic. For a registered read,
it rewrites the defining address at the read's original state and names
that rewritten read. It does not add the owner's alias displacement to the
loaded value. Resolving the new address against the original state keeps
cached child identities across a joined loop; a projection for the old address
alone is insufficient. Naming uses exact recorded reads and cached pointer
cells; a cold read keeps its state application without searching history.
A complete pointer value cached at the rewritten address is returned directly
from that state, including after a pointer store.
The joined-pointer-field fixtures cover the explicit
rewrite and rejection of an equality about a different field.

Recursive resource child indices use the same term-definition interface.
After a child expression passes the existing readable-expression and argument
checks, its certified typed producer metadata is retained before the temporary
fact stream is discarded. The cached scalar-cell conversion preserves this
metadata just as the symbolic pointer-read route does. Ordinary propositions
and volatile reads cannot supply it. `mdtests/egraph_recursive_child_alias.md`
checks unfold at one parent form and fold at an equal model identity,
without intermediate field-load claims or C writes. This does not transport
loads across different states.


A pointer read's address base is `AddressBase::Load(load)`, where `Load`
(`src/kernel/primitives/load.rs`) is the interned identity of one cell's bytes
at one version point: interned by the point's read key and the cell, and
carrying that point and cell so decoding it needs no registry lookup.
`Load::at` is its only constructor and `Load::base` the only builder of the
base (`build_support/read_construction.rs`). The key holds no pointee type,
no object-or-function category and no selection kind: one cell at one version
point is one load at every pointer type, an exact and an indexed selection of
one point are one load, and a store at one object-pointer type answers a load
at another (`design/loads.md`, "Pointers";
`mdtests/a_pointer_store_answers_a_load_at_another_pointer_type.md`). The
category belongs to the decoding: a store lookup for a typed value passes the
category of the value's type, so a function-pointer store answers no
object-pointer decoding, nor the reverse; a lookup about the base as an
address asks about the cell's bytes and accepts a store of either category.
The equality graph indexes this explicit pointer application without consulting
the scalar load registry's mutable access width. Ordinary C pointer-load
producers still create the storage-relative form; their checked path-context
bridges relate that form to the explicit graph term. Making the explicit name
the execution value is a separate proposal that would require a coherent
review of materialization, substitution, provenance, and rendering. Merely
swapping the constructor breaks existing verification and expansion fixtures.

An integer or float read, `MachineTerm::MemoryLoad`, has the same `Load` as
its identity, beside its kind and the producer's selected point
(`design/loads.md`, step 3a; [resource tracker](resource-tracker.md#a-load-term-carries-its-reads-kind)):
comparing two reads compares one id and a kind, not their addresses.

Pointer classes are weighted:
`base(member) = base(representative) + delta`. Exact affine normalization can
relate displaced forms such as `p + 8` and `(p + 4) + 4`. Preserve signedness,
bit width, wrapping, and definedness obligations of the supported C semantics;
do not distribute arithmetic through a wrapped index as if it were an
unbounded integer.

The graph records an exact offset equality when a congruence merge joins two
pointers already in one block class. Account for affine expression size when
describing merge cost.

### Loads and memory states

Model a load as an application keyed by its state, address, and access
interpretation (sort/width and any other distinctions required by memory
semantics). The semantic key is explicit even when an external registry
supplies it.

The typed graph query uses a distinct pointer-load name and an explicit
loaded-pointer address-base variant, rather than hiding another sort in the scalar
load-variable range. Its key is the assumption-free canonical state,
address, and pointer interpretation (object-pointer value, eight-byte access).
Pointee type remains on the C value and is not key material. Live origin/epoch
metadata is separate from that defining key. The widthless scalar load
registry's mutable maximum-width field does not decide membership in the
pointer-load application index.

Do not emit a scalar equality between a pointer-load name and a widthless
`MemoryLoad`. The pointer registry defines the graph application;
scalar bit views need their own checked conversion. A materialized pointer cell
already contains its value: reuse that value, including a retained value across
havoc only through the existing checked retention rule. If a future change
uses the graph's explicit loaded-pointer node as the C execution value, its
constructor, decoder, substitution, provenance, and rendering consumers must
be reviewed together. The current equality query requires none of that.

Equal addresses at one state imply equal compatible loads. This must hold
whether the loads were registered before or after the integer address equality, and
whether either load already belongs to another explicit class. For example:

```text
p == q
load(M, p) == x
load(M, q) == y
----------------
x == y
```

The answer must survive extra facts and all insertion orders. Nested loads
must obey the same rule without a fixed nesting-depth limit.

For 8-, 16-, 32-, and 64-bit integer reads, a recorded store equation
`load(M, p) == value` and the integer address equality `p == id` establish
`load(M, id) == value` by ordinary congruence. Registering the read alone
supplies no cached value. Lowering keeps the read's own term and does not
respell the address through the equality (lowering is fact-stable,
[raise-lower principle](raise-lower-principle.md#lowering-is-fact-stable)). Both equation-before-alias
and alias-before-equation admission orders work, without enumerating aliases
or reading the memory's cached values.

Function-pointer stores retain the complete typed equality between the read at
that store's state and its supplied function value. A function read registers
its state/address application; ordinary congruence propagates the explicit
fact through aliases, including aliases admitted later. It does not enumerate
an address class, consult cached cells, or retry cached lookup after a union.
The separate data-pointer checked-read/provenance machinery is unchanged.
Regressions include `function_pointer_read_requires_explicit_store_equation`,
`function_pointer_read_query_does_not_scan_aliases_or_cells`,
`a_wide_read_requires_an_explicit_store_equation_even_through_aliases`, the four
narrow `*_read_requires_store_equation` tests, and their scaling tests.

A word that a recorded true 64-bit equality equates with an expression
naming a pointer address is also filed by class
(`TermClasses::wide_equation_endpoints`, merged smaller into larger); other
equalities file nothing. The integer-to-pointer cast, recovering a pointer from
`word == address(p)` (`pointer_tags::form_of`), finds such a fact about every
word equal to its own in one class lookup. It cites the recorded fact; the graph equality it crossed is not a
named premise, so the record cannot certify. The graph's numeric-address
forms still authorize no conversion. Regressions:
`mdtests/packed_pointer_loop_object_class.md` and the scaling test
`a_recorded_address_fact_is_found_through_its_word_class_without_scanning`.

Different states do not become equal merely because addresses match.
Execution may preserve a load name through its existing checked unchanged-cell
rule. Additional frame reasoning belongs to explicit transport or the checked
execution rule that needs it, and contributes justified equalities to the
path. Equality comparison must not walk memory history or call a frame prover.
Do not scan all earlier loads to choose a convenient existing name.

### Provenance and separation

Value identity and proof of separation are different information. An opaque
pointer alone does not establish which allocation it can reach. Preserve
separation using evidence justified by supported C semantics, ownership, and
lifetime/reachability rules. Equal values must have consistent provenance
information, but mere inequality of term IDs proves no separation.

Do not infer a pointer's provenance from the representation of the cell that held
it. Do not infer an allocation's birth from a contract allocation claim or
from absence in a projected state. The existing special rules for hidden
locals and later-declared locals need their exact preconditions retained.
Any broader rule needs its own positive and negative tests.

Memory states form a DAG. A proposed class attribute such as "earliest birth"
needs a semantic ordering and evidence valid in the current path; state IDs
or unrelated branch timestamps do not provide that ordering.

## Incremental closure and indexing

Maintain an application-signature table and parent-use lists alongside the
persistent equivalence relation. When child classes merge, reconsider affected
parent applications, merge signature collisions, and continue until the pending
work is complete. Queries may register their explicit terms, but must observe
a closed state before returning. Batching is allowed only if it preserves this
boundary and charges the actual maintenance work.

`EqualityGraphState` stores
load applications (`loads`), block use lists (`uses`), application signatures
(`signatures`), and reverse signature bindings (`load_signatures`). Registration walks only a query's unregistered load-address
dependencies; merges reindex users of moved blocks and enqueue colliding load
values for merging. Every registration/merge drains the worklist before return.
Class weight counts blocks and application uses, so high-fanout classes remain
on the heavy side of a merge. A context clone copies persistent roots into its
own lock; query registration cannot mutate a sibling's closure.

Signature keys (`LoadSignature`) contain state arena identity,
representative block identity, an affine-offset ID, and the load kind. Offset sequences are interned with shallow prefix keys
and retained machine-atom IDs. This removes deep state/term comparison from
signature lookup. Explicit affine syntax is normalized with an iterative walk;
legacy printed output sorts structurally rather than by interning order.
The existing weighted affine payload operations still need broader scaling
review for growing symbolic deltas. Same-block equations and equality between
offset atoms are not yet incorporated into this closure.

Registered pointer-width loads in opaque symbolic-block form enter this
application index. Ordinary C load construction retains its existing encoding;
checked read-site equations connect its values to the graph's applications.
Pointer comparison uses that closure directly. Read/fold resource indexing
has its own ownership and range-coverage boundaries below.

Resource lookup pairs persistent resource roots with the trusted graph's
pointer-class merge stream. Memory facts have a raw block/affine-base index
maintained at insertion and removal, so a cold lookup can pair that index
without scanning the resource store. The initial execution proof boundary
registers the selected resource input's starts as typed graph address
applications. Successors register only newly published occurrences. A paired state retains both resource and graph checkpoints;
execution proof-step boundaries advance it using exact occurrence deltas and
class merges. Forks share those roots and have independent cache locks.
A restricted or sibling context starts from raw roots and its own graph's
merge stream, rather than retaining unsupported address associations.

Each class has a persistent affine-address bucket. Its coordinate origin may
differ from the graph's representative: a merge keeps the larger **resource
payload** and shifts only the smaller payload, even if the graph's block/use
weight chooses the other representative. This avoids repeatedly rekeying a
large resource bucket when it acquires resource-free aliases. Queries select
symbolic ranges at the requested affine base, or concrete spans selected by
their canonical starts (including the predecessor and starts inside the
requested span). The resource algebra then checks access mode, quantity and bounds; an indexed equality grants no
ownership. Full resource normalization refreshes the derived payload during
its existing complete-input operation because normalization can renumber entry
IDs; ordinary deltas do not rebuild it or scan exact-fact buckets.

Fold consumption uses this paired address/span index instead of enumerating
pointer forms. A selected candidate can express the requirement in its
own block coordinates using the graph's affine relation; this visits no other
class members. Existing local range matching remains responsible for
same-block containment and endpoint reasoning.

Logical model reads retain the selected supplier's full base expression when
choosing its address coordinates. A loaded pointer can have a variable offset
within its storage block; only the displacement from that complete base needs
to be constant. Dropping the offset would give an unrelated read identity for
an unchanged field after a helper call. Address selection grants neither read
permission nor equality between different states.

Specification reads also use the paired index for concrete affine addresses in classes whose memory entries
all have positive concrete read cores. A persistent AVL interval tree stores
each occurrence's byte start/end and each subtree's maximum end. It lazily
selects ranges covering the access's candidate footprint, including mixed spans and overlapping
views where the nearest predecessor is too short. A read stops at the first
candidate accepted by the ordinary permission and bounds checks; it does not
materialize every overlapping view. Updates copy only the affected tree path,
and class merges shift only the smaller resource payload's interval tree.
The occurrence count detects incomplete index coverage. A miss is final for
a complete concrete fragment; incomplete fragments use the bounded candidate
classifier described below. Positive hits retain their suppliers even when
coverage is incomplete. Neither case scans unrelated resources, including
resources published before a later integer address equality.
Whole-cell read hits also use an exact-start payload attached to typed graph
address classes. Offset congruence and late same-state loaded-pointer
merges update this payload through the graph's persistent term-merge stream.
Block merges translate only affected registered address applications. Payload
unions retain the larger entry set, even when the graph chooses the other root.
Raw offsets and their affine normal forms are definitionally connected inside
the trusted graph; this registers no proposition or ownership premise.

Each exact-start class indexes eligible occurrences by authorized read
footprint. A known equality selects only entries of the requested footprint;
different or unsupported read shapes at that address or elsewhere in the block
class do not disable the match. Registration, removal and class merging update
both the complete fold-candidate set and these read sets. Each occurrence
contributes at most two footprints (including the logical pointer-slot rule),
and merges move both indexes from the smaller occurrence payload. Input
registration still belongs to the execution proof boundary. An unbound class
is unknown: scalar arithmetic or state transport may justify an equality
outside this closure, but permission lookup cannot search for that evidence.
Candidate delivery is lazy; equality selects the
occurrence's own start and the ordinary checker still validates its quantity,
access mode, and bounds. The logical four-byte pointer-slot convention remains
unchanged, including interior reads of longer int32 ranges, which cannot use
the whole-cell path. Unrelated scalar equality does not disable this cell
fragment. The same address payload supplies fold candidates, whose coverage
and consumption checks remain authoritative. Cold lookups cannot trigger full
input registration; the shared classifier uses retained evidence or refuses
unprepared selection. A proof boundary establishes input publication. Branches inherit registered
persistent roots. Pairing keys cached views by the persistent history of
admitted pointer, offset, int32, and checked-read equalities, independently of
query registrations. The initial boundary registers a premise-free resource
checkpoint for that lineage and a current view using the source's already
closed graph. It does not reconstruct the current closure by walking admitted
input history.
A pure branch created before publication, or a sibling with different inputs,
therefore shares the registered resource payload without importing another
graph's local node IDs. This preparation changes no proof-context fact.

Each derived view owns a graph checkpoint. Later inputs apply only the delta
from its cached ancestor. Resource mutations advance the registered root and
published view; other cached forks remain persistent lazy views. A single first
memory delta stays on the empty checkpoint until attachment, allowing that
branch to adopt its already closed graph without processing unrelated inputs.
The next mutation flushes both deltas, so pending resource work cannot grow
with the ambient context. Ordinary queries register only the requested address
and any remaining resource delta. Pointer/address merges move affected payloads.
Read and write candidates retain that checkpoint for address translation, and
fold selection uses it for both endpoints. Switching between parent and sibling
views preserves their persistent roots instead of discarding the complete
payload and falling back to a resource search. Full normalization already
visits its input: it refreshes the registered root and published view against
new live occurrences there, discarding other cached views with obsolete IDs.
It retains their graph states, scans no equality history, and leaves no full
registration pass for a later lookup. A cold view made before publication
cannot shadow a completed registered ancestor.

An index with no memory occurrences has no class-keyed IDs to translate. It
captures the already-closed source graph in constant work. The first memory
occurrence can therefore use that state, including in a preexisting
sibling, without walking unrelated scalar equality inputs. Empty-input
capture and subsequent attachment have deterministic scaling regressions.

These admitted-input records are trusted internal index plumbing, not an
`explain` API, generated proof steps, or a second equality theory. They apply
existing admission rules and never scan the proof context for premises.
Regressions cover forks before publication, publication under one sibling's
facts, repeated switches between views, read/write/fold selection, completed
reads, branch isolation, real normalization replacements, and deterministic
work over growing resource inputs.

The read/write candidate contract retains the selected query, resource
occurrence IDs, and their paired graph checkpoint together. Address alignment
accepts an occurrence ID and reads its range from that retained checkpoint;
consumers do not supply an alternate query form or reconstruct a range.
The direct ownership-support consumer uses the same retained alignment, then
restores the requested range's base from its checked start displacement. It
never asks an ambient graph that may lack the selected loads' registrations.
Whole-cell alignment checks the query against the occurrence's start in the
trusted graph. Interval alignment uses the checked affine block relation.
Neither path grants authority: the ordinary permission, width, and containment
judgments still decide whether the selected occurrence supplies the access.

Interval completeness is local to the registered affine address block class.
The graph maintains whether non-affine offset equivalences reach that class
through registered application dependencies. Unrelated scalar aliases do not disable concrete interval queries. This metadata is persistent, follows
late merges and block relabels, and applies to subsequently registered parents.
Affected classes report unknown coverage; exact whole-cell evidence remains
usable independently. Concrete loaded pointers use the interval contract after their retained
definitions register; there is no blanket exclusion of loaded-pointer address bases. An unpublished
loaded-pointer interval remains unknown: its raw structural root has not
registered all suppliers' retained origins, and a simple query cannot do that
whole-input work. Publication establishes this fragment's completeness.
Producer metadata indexes the read atoms in kernel-minted storage-relative
names, so a shifted expression registers its original defining read directly.
Exact address evidence therefore applies to shifted names too. Storage-relative
names whose affine coordinates remain symbolic report unknown interval
coverage; the symbolic containment support below handles that case.

Completeness propagation uses a separate subset of the graph's parent-use
index containing only applications whose status can still change. Once an
application is affected, its edges leave that subset. Otherwise a new alias in
each sibling could revisit already-affected parent applications and make fork
checking quadratic. Each changed application is charged once along a branch;
class merges move the smaller payload and query checks inspect a class marker.
Multi-size regressions cover unrelated scalar facts, same-class non-supplier
ranges, and repeated forks beside already-affected parent applications.
Unsupported range coordinates, incomplete read-core coverage, and unregistered
fragments report unknown when the shared candidate service below cannot select
a checked supplier. General permission queries refuse these cases without a
compatibility search. The interval summary is part of the trusted kernel's derived index;
it creates no proposition or access capability.
Candidate footprint calculation shares the kernel's existing logical
pointer-cell rule: a pointer read may use one 4-byte logical element, while
other element widths still need their own full range check. The index must not
silently tighten that rule to physical pointer width.
Deterministic regressions cover late aliases,
nonzero displacement, branch isolation, insertion/removal and normalization,
growing alias classes, disjoint spans sharing one base, concrete read hits and
misses, mixed spans, overlapping views, lazy delivery of covering ranges,
interval updates against an independent model, and incremental merges
with a large resource payload. Resource-section publication uses the expansion
delta rather than recreating views for unrelated ambient memory ranges.

Write-resource candidate selection shares the complete affine interval
summary. It selects covering occurrences lazily, translates the access into
each owner's block through checked graph equality, then applies the existing
write-permission and bounds judgment. Views cannot supply write authority.
The interval index maintains a separate owned summary, so selecting write
candidates does not enumerate overlapping views. Both summaries receive the
same occurrence updates and smaller-payload class merges. A deterministic
regression measures write lookup beside 16, 64, 256, and 1,024 covering views
with one owner; lookup work must remain independent of the view count.

Composite fold argument and body lowering uses the operation's retained
`PureFactContext`, including its trusted equality graph and checked bounds.
Witness selection and reconstruction of the selected resource for the kernel
certificate retain that context too. The assumption handle is persistent;
these calls neither reconstruct the ambient fact list nor register ambient
resources during a read query. A reduced fold of `tag(q[i])` through a view of
`p[0..n]` uses checked `p == q` and `0 <= i < n`, expands, and independently
reverifies. Dropping the equality or either bound refuses the read. General
permissions share the bounded supplier service below.
An indexed miss or failed candidate check is decisive for this covered
fragment; it does not retry other forms or scan the remaining resources.
Whole-cell writes additionally use a separate footprint payload containing
only positive concrete owners at registered typed address classes. Late
offset and loaded-pointer equalities update this payload through the graph's
existing merge stream. A selected occurrence supplies its own start address
for the authoritative range check. Views never enter the write payload; an
exact-size view cannot hide a larger owner. The read and write payloads share
the existing footprint/width eligibility rule and move only the smaller
occurrence payload on a class merge. Exact candidates do not depend on an
affine coordinate bucket. Unbound footprints and unsupported containment or
state shapes proceed through the shared candidate classifier below; when
it cannot select a supplier, permission is refused. Unknown equality is not
disequality. The existing logical pointer-cell width
rule is preserved for both access judgments. Input registration remains a
proof-boundary operation, not a scan performed by a cold lookup.

Address-class queries register the same retained logical-pointer definitions
as pointer-equality queries. Registration visits only the requested term and
its recorded producer dependencies, then closes them against the current
branch's equalities. A resource lookup therefore needs no preliminary equality
query to recognize `load(a)` and `load(b)` after proving `a = b`. It registers
no unrelated reads or resources and introduces no premise or access authority.
The regression asks the read and write indexes directly before any equality
warm-up, rejects sibling, displacement, width, and state mismatches, and
checks cold address registration at multiple unrelated-definition counts.

Structural "already held" range checks do not scan an address base's
resources. They use a publication-maintained index of base shapes and affine
origins, plus the raw interval summary for complete concrete coverage at a
plain origin with constant displacement. Updates and consumption maintain
persistent roots, and branch copies share them. Reads use the shared graph
candidate service.

The structural index is part of the trusted kernel. Shape fingerprints ignore
states only to select candidates for the existing structural judgment; a
hash match or collision never proves pointer equality, range containment,
initialization, or permission. Each selected occurrence still passes the
original range check. Proved graph aliases do not become structural matches.
Multi-size regressions cover cold hits and misses beside unrelated pointer
parameters, and controls cover partial ranges, consumption, and branch isolation.

General read/write permission uses the shared candidate service described below, with bounded refusal
outside its supported fragments. Checked resource construction owns attachment: an empty input captures the closed graph
before insertion, and composition advances a prepared lineage. Normalization
already visits its full input and publishes even when no representation changes. These boundaries also
cover temporary contexts built during resource-clause evaluation, independent
of the surface execution-step wrapper. The temporary context for checked
composite/borrow projection evidence also uses checked construction. It starts
with only the selected composite head; removing that head and adding dependent
children retains the graph attachment, so a prior child's whole-cell payload
can be selected through transitive integer address equality. This is part of the
trusted kernel and changes candidate selection only: checked expansion and the
borrow ledger still establish the exact parent, children, and authority. Logical
contract loads can bypass permission lookup, so regressions inspect the actual
projection input's attachment in addition to checking expansion and borrow
controls. The owned one-level frontier used to adapt a composite view to borrow
backing uses the same checked construction. Its temporary context contains only
the selected owned head, and dependent child deltas retain the attachment. This
does not authorize a lend: the adapter still checks the caller's owned coverage,
definition facts, and recovery recipe. The coverage context reconstructed from
that owner's checked children also uses checked construction before consuming
the requested frontier. It retains graph candidate selection while ordinary
resource consumption checks quantity, ownership, and sufficient coverage;
partial consumption leaves only the residual authority in a proof-local fork.
Branch isolation, read width, double consumption, partial coverage, state
isolation, and scaling against unrelated facts and caller resources are covered.
Normalization refreshes existing attachments when it replaces occurrences.

The non-consuming `ResourceContext::satisfies_fact` query also selects memory
occurrences through the graph's address index. It shares consumption's helper
for expressing a requirement in the selected occurrence's block; the helper
preserves bounds, element width, and access mode. Ordinary resource entailment
then checks the available authority and byte coverage. For example, after
consuming `a[0..1]` from `a[0..3]`, a context with `a = b = c` recognizes
its residual `a[1..3]` as satisfying `c[1..3]`, without restoring the consumed
prefix or changing either retained representation. This graph and its index
are part of the trusted kernel. Regressions cover sibling-context isolation,
view refusal, insufficient coverage, preserved states, and multi-size
scaling beside unrelated resources and equalities. The retained supplier
interface below also covers explicit fragment composition; unsupported
symbolic matching refuses without an ambient retry.

An unchecked context with no attachment remains unprepared. Extending a valid
ambient context through a delta-only API does not silently publish all its
unrelated resources; use a whole-input normalization/publication boundary when
attachment is required. Unsupported symbolic containment and retained
load-origin forms refuse when the indexed service cannot select a supplier. Forks of a published
input retain their pairing. Address anchors alone are not a substitute for
attachment. Stored-value and initialization-evidence lookups use their own
form indexes.

Checked additive producers retain one form per index width in both address
classes and offset classes. Same-block pointer comparisons can enter as offset
equalities; those forms are applied only in the queried pointer's own block
and cannot identify unrelated blocks. A wide-view requirement selects a checked
uint64 displacement instead of losing its window bounds in an equal signed or
mixed-index expression. Payload lookup and class merging use a constant number
of indexed entries. The original span and permission checks still decide
whether the selected supplier covers the requirement. Regressions cover missing
aliases, short spans, mixed prefixes, block isolation, and increasing numbers
of aliases.

Read, write, and fold consumers are integration examples. A lookup must not
enumerate every form in a class. Equality indexing narrows candidates;
permission quantities, range containment, ownership reservation, and ordering
still require their own checked judgments and complete candidate indexes.

## Bounded symbolic containment support

Symbolic endpoints cannot in general be sorted into an interval tree. The shared
resource/graph pairing therefore maintains an additional persistent index
for exact symbolic byte footprints beside the existing exact start-address index.
A footprint is a typed
graph application of its start and end address classes. Congruence propagates
late base, scalar endpoint, and retained same-state load equalities through
that application. These applications and their occurrence payloads are part of
the trusted kernel. They establish neither coverage nor permission.

`symbolic_range_read_supported(required, assumptions, supplier)` returns
`Some(true)` or `Some(false)` only after selecting one supplier and checking its
ordinary read core with `memory_range_covers`. `None` means supplier selection
is unknown. The selection rules are:

- An explicitly supplied `ResourceOccurrenceId` must resolve to a live entry in
  this resource checkpoint. An obsolete occurrence cannot authorize a read.
- Otherwise, a sole occurrence indexed by the requested symbolic footprint is
  selected. If that does not identify one, a sole occurrence at the known-equal
  start address may be selected and its bounds checked arithmetically.
- An ambiguous bucket is inspected for cardinality only. The checker does not
  iterate symbolic partitions looking for a successful coverage proof.

The underlying selection service keeps a separate owned-footprint index for writes;
view evidence is insufficient and the selected owner's quantity must be positive.
Concrete whole-cell and interval selection remain in their existing indexes.
Concrete ranges do not register every end address as a new graph dependency:
that would make merging a cell base visit all differently sized concrete spans.
Payload updates occur at publication and resource/class deltas, with smaller
payload merging. Simple queries register only their explicit footprint.

Evidence reaches source verification through existing checked resource
requirements and footprints, rather than serialized graph class IDs. A
checked `views p[i..i+1]` requirement supplies a directly indexed range;
a resource/borrow certificate that already selected a supplier can retain its
opaque occurrence handle. Expansion emits ordinary proof source, and fresh
verification reconstructs its checked occurrences and graph registrations.
Borrowed byte and halfword buffers, including nonzero symbolic starts, have an
expansion/rechecking regression. Kernel regressions cover symbolic index bounds,
late endpoint equality, states, sibling contexts, retired occurrences,
read/write authority, and same-base non-supplier scaling at multiple sizes.

The symbolic-byte-span consumer uses this service exclusively. Unknown or
ambiguous selection refuses without an exact-base retry or whole-input
scan. After selecting
one supplier, the checker inverts explicitly scaled byte counts into that
supplier's element width before ordinary coverage arithmetic. It checks the
selected read core, including quantity; equality does not supply authority.
Consumer regressions cover byte, halfword, and wider footprints, bounded
subranges, missing bounds and aliases, sibling isolation, view and owner
suppliers, and zero quantity. A regression rejects an ambiguous start bucket even when a
hidden search could find a covering supplier; checker and persistent-index
work remain flat across 16–1,024 same-base ranges. Storage and object
consumers use the indexed evidence described below.

General read/write permission uses one shared classifier. Exact address/start
payloads include eligible partial reads; physical interval hits select retained
suppliers even when the index cannot establish complete coverage. A miss is
final only for a complete concrete interval fragment. Otherwise, prepared base
and affine-class summaries can select a sole supplier by cardinality. Symbolic
read starts have their own class payload, so a partition rooted in an outer
storage block does not hide its logical pointer base. A multi-size regression
selects the left partition beside unrelated same-base ranges without searching
them; missing bounds and view-only write authority still refuse. Ambiguous
or unsupported queries refuse before checking. No consumer retries other forms,
searches a block/frame, or tries another strategy after a failed supplier check.
Views supply read authority; writes select owners. Quantity, alignment, width,
signed bounds, initialization, and no-wrap obligations remain checked separately.

Each address has a stable raw application connected to its checked affine
projection. Completed typed-read equality joins those address applications as
well as the pointer equality service. Explicit query subterms register before
pairing class deltas with resource payloads. Opaque pointer-read tokens cannot
be treated as ordinary offsets using coarse block membership: their supplier
base must have a checked graph bridge to the query. Persistent siblings retain
their own admitted read evidence.

`MemoryAccessCandidates::address` aligns the query against the selected
occurrence's base using the same retained graph. It preserves explicit byte
increments and their bounds obligations. The unchanged alias store `q[i] = 7`
with `p == q` and `owns p[1..n]` verifies, expands, and independently rechecks;
missing equality, bounds, and write authority still reject it.

Function entry and certification publish selected inputs at their construction
boundary. Clause prefixes capture their checked graph while empty and maintain
occurrence deltas as they grow. Proof roots and planners use `from_source` to
retain the graph instead of rebuilding a fresh lineage from a proposition
vector. Reused borrowed-input authority and certification caller states pair
against the new claim's premise context at those explicit producer boundaries.
The shared kernel contract-entry builder also pairs its selected caller and
entry input before clause evaluation; independent certification uses that same
entry interface. The surface entry view pairs its selected resource input
after choosing the kernel-admitted premise list, before execution starts.
Permission queries never initialize an index by traversing ambient input.
Deterministic regressions measure checker and persistent-index work beside
increasing unrelated resources, same-class views, late merges, and forks.

## Retained memory support and fragment consumption

`MemoryFactCandidates` is the shared memory-supplier interface for satisfaction,
direct fact support, owned support (including its other-support check), and
incremental consumption. It retains original entry IDs and the paired graph
checkpoint. Requirement alignment uses that checkpoint rather than a pointer
form selected from an ambient graph. Direct support returns the original
held representation; owned support returns its original occurrence. A supported
projection must still name a live owner matching its recorded dependency.
The graph and this derived candidate evidence are part of the trusted kernel.

Candidate selection first admits exact typed footprints (including explicitly
supplied unpublished inputs), then uses graph symbolic footprints and intervals
covering the whole requested span. The fragment frontier includes intervals
covering its start and starts inside its explicit concrete byte span. A sole
indexed symbolic supplier can be checked; ambiguous unsupported selection
refuses without block or shape searches. Ownership selection excludes
nonpositive quantities. Ordinary resource judgments check coverage, access
mode, quantity, width, and the operation's separation policy. Equality supplies
no resource or borrow authority. Candidate delivery is lazy: a direct proof stops
at its first checked supplier rather than collecting all overlapping views.

Constant spans also have an interval index relative to their complete base
address class. This retains constant-offset bases as well as symbolic bases:
a checked pointer alias can select an interior field of a returned range even
when affine block coordinates cannot express that alias. Read and owned
intervals retain their original occurrences; late base equalities merge only
the affected smaller payload. Queries follow their explicit additive prefixes
and interval-tree paths, without scanning other ranges sharing the base.
Candidate alignment and ordinary coverage still check bounds, widths, access
mode, and quantity. Partial consumption removes the original interval and
publishes its residuals; a view cannot become an owner through base equality.

When the request needs several fragments, the checker composes only its
selected supplier input and computes residuals there. Symbolic fragment chains
follow a unique indexed start at each selected endpoint. Ordinary coverage
checks that a fragment lies inside the explicit request before traversal
continues, and ambiguity or a repeated occurrence stops the chain. Starts are
looked up by typed address class, so proved endpoint aliases reach the same
retained owner payload. Indexed lower bounds incident to the requested start
can name a unique residual start (for example, `i < j` reaches `i + 1`).
That bound selects an occurrence; it never grants coverage or ownership.
Constant queries do not inspect a shared literal's bound neighborhood.
Explicit base displacements are folded into object-relative candidate
coordinates once, covering both `p[j..j+1]` and `(p+j)[0..1]`. Stored pointers
and resource facts retain their original terms. Modular coordinate agreement
is only candidate selection; ordinary numeric coverage and merging still
reject wrapped, non-adjacent physical footprints.
This pays
for selected fragments rather than walking unrelated same-base holdings.
It does not normalize unrelated holdings or retry an ambient matching route. Borrow-bound and projected
observations keep their original dependencies and cannot be coalesced this way.
Persistent edits install residuals in the consuming fork; siblings retain their
input. Empty range identity
asks the shared graph whether its endpoints are equal.

A transitive-alias regression checks that direct support returns the actual
retained owner and occurrence through the shared candidate interface.
Multi-size regressions
measure satisfaction, support, and two-fragment consumption beside 16, 64,
256, and 1,024 unrelated same-base spans. Controls cover holes, insufficient
coverage, residuals, missing aliases, view-only authority, zero quantity,
sibling states, and the existing projection/separation checks. Another
scaling regression checks direct support beside 16–1,024
overlapping views, including insufficient views inserted before a sufficient
owner; explicit fragment composition is measured separately
over increasing selected input sizes. Symbolic-chain and ordered-residual
regressions also measure work beside unrelated holdings.

## Storage authority and object provenance

The graph and these derived indexes are part of the **trusted kernel**.
`owns_storage_access` uses the shared write candidate classifier and retains
its selected occurrence and graph checkpoint. It checks positive ownership
and the complete byte footprint with ordinary resource entailment; write
candidate eligibility alone is insufficient. Allocation-retirement coverage
uses this interface for concrete byte counts and shared fact support for
symbolic footprints. Neither path scans a block for an owner.

`memory_object_evidence` selects a retained nonempty footprint using the
pointer's C object identity, separately from its raw address. Exact object
payloads are maintained with resource deltas, including on raw explicit
inputs. Published payloads follow typed object-class merges in the same
private graph checkpoint. Known nonempty footprints select a witness directly;
a unique symbolic candidate still requires ordinary nonemptiness and positive
quantity checks. A cold miss refuses without walking equality history or
publishing a context at lookup. Consuming an owner removes its witness only
from the consuming resource fork. Integer address equality between different external
objects does not merge their provenance identities or create storage authority.

Pure composition provenance has a private `ObjectEvidenceSources` interface.
It retains the first source context and its persistent indexes in constant
work. Persistent checkpoints retain each admitted source lineage. Later
admissions follow ancestor or sibling deltas to their common prefix, filter
for inputs actually present in the admitted source, and never traverse the
shared history. Independent sources add their explicitly supplied memory input
once. Querying this evidence visits
neither the ambient composition collection nor its resource inputs. Its
backing context is private and cannot be consumed as resource authority.

`EqualityGraph::storage_address` preserves the original address unless retained
concrete evidence can name its storage coordinates. Exact typed address
payloads retain original concrete inputs; affine classes retain a unique
concrete block anchor. Both summaries follow persistent class merges. This
handles transitive aliases and multiple external addresses sharing one raw
address-space block. Generated representative projections never mint storage
evidence. Ambiguous evidence, unsupported arithmetic, and arithmetic overflow
leave the address unresolved. This query establishes no ownership, object
provenance, lifetime, bounds, initialization, or writability. Mutex
initialization and runtime storage havoc use it to identify the storage they
subsequently check or affect. The shared alignment checker accepts this one
checked concrete formation as well as its original formation evidence;
mutex initialization does not retry alignment on another pointer form.
Explicit power-of-two alignment premises also supply one retained witness on
an address class. Late equality merges keep the strongest original premise;
lookup checks that premise directly instead of enumerating class members.
This supports symbolic aliases as well as concrete storage coordinates.
The formation rule retains any explicit alignment premise and still checks
byte displacement, intrinsic alignment, and requested alignment. The existing
explicit alignment normalization step encodes only formation arithmetic;
its evidence producer refuses a class witness whose supporting equalities
are absent from the selected premises. Ambient alignment checking does not
label such incomplete evidence as a complete proof.

Block-index visits apply effects or check all affected occurrences; they do
not search for an implicit memory supplier. Explicit composition/publication and fragment
inputs may be visited proportionally to their admitted input or produced delta.

Regressions cover transitive ownership aliases, view-only and zero-quantity
refusals, typed object identity versus raw integer address equality, empty footprints,
consumed occurrences and persistent siblings, concrete storage anchors and
ambiguous classes, and several external addresses mapped to distinct storage.
Multi-size checks cover unrelated same-block footprints and composition
sources, hits and misses, and growing alias histories. Existing initialization,
retirement, composition-admission, and contract-projection scaling controls
remain in force. The complete fixture gate verifies expansion and rechecking.

## Resource producer publication

Fresh selected-resource assembly starts with
`ResourceContext::new_with_equalities(assumptions)`. This kernel service captures
the current closed graph while the resource input is empty. It costs constant
work with respect to ambient resources and equality history; subsequent facts
maintain the paired index through existing resource deltas. It does not check
validity, create authority, or normalize representations. Selected facts still
pass their existing resource, borrow, expansion, or certificate checks. The graph
and these indexes are part of the trusted kernel.

The constructor is available inside the crate because surface proof assembly
also creates temporary inputs to kernel resource queries. It does not expose
graph mutation outside the kernel. `unchecked_with_fact(s)` retains an existing
attachment but never publishes an unrelated ambient frame. Use checked
composition when the facts' validity needs checking; its empty-input path
already captures the graph. Whole-input normalization is another existing
publication boundary, including a normalization that changes no representation.

Producer families publish as follows:

| Producer family | Publication rule |
|---|---|
| Function-call single-view satisfaction, conditional-control frontiers, returned composite/population bodies, and access-mode refinement | Fresh assembly captures its actual assumptions before adding selected facts. |
| Framing and owned-footprint derivation, matched-instance body evaluation, and selected instance load values | Fresh selected heads/ranges start published; expansion deltas preserve attachment. |
| Contract transfer, returned-clause evaluation, allocation support, and definitional resource consumption | Fresh requirement/supply/frontier contexts capture the assumptions used by their consumers. |
| Stable-view planning and borrow entailment | Fresh callee and single-supplier contexts start published. Binding checks that intentionally exclude ambient facts use one empty proof context for both construction and entailment. |
| Kernel execution certificates and population authority exchanges | Checked temporary child, authority, and support contexts start published under the certificate's local facts. Path preparation publishes explicitly substituted exit resources once before individual claims query the output. |
| Loop body reset and borrowed contract input installation | Fresh live contexts capture the current assumptions; selected-view/instance deltas retain their parent's publication. |
| Surface dynamic view dependencies, checked returned-resource receipts, and compact composition propositions | Fresh contexts capture the same assumptions used to check their occurrences or receipts. Existing occurrence and borrow source is preserved. |

Existing checked constructors in composite projection, owned-frontier expansion,
frontier coverage, mutex transfer, and object-comparison support remain unchanged.
Explicit supplier composition in resource consumption starts with the
selected checked input and publishes its normalized result before consumption.
It does not select through a structural or ambient normalization retry.

The retained raw constructors are intentional and have different lifetimes:

| Retained raw input | Why no graph attachment is required there |
|---|---|
| Empty join-abstraction shapes and checked-return certificate placeholders | Used for structural comparison or replaced by checked clause contexts; no unchecked memory is inserted for a live query. |
| The empty residual in reconstructed `CallKeptOwnership` and the empty transfer used when composing borrow evidence | They remain empty; actual authority is carried by the recorded ranges or checked borrow evidence. |
| Startup static-resource construction | Builds provisional program data before proof assumptions exist. Its live execution input is published at the explicit proof boundary, not by permission lookup. |
| Bitvector/pointer substitution of theorem/state resource terms | Rebuilds structural proof payloads without current assumptions. Old graph equalities cannot be inherited after variable substitution. A live instantiated input is published when admitted to execution. |
| Surface composite-body instantiation and branch-interface collection | Provisional lowering output is explicitly checked/composed before becoming live authority; no permission query attaches it implicitly. |
| Instance field scope and default empty `ExecutionState` fields | Lexical instance interpretation or empty data, rather than a memory-authority context. Live resource assembly uses the rules above. |

A new producer must choose one of these publication boundaries and document any
raw lifetime. Do not repair a missing attachment by scanning a cold frame from
a query, and do not call whole-input publication repeatedly for deltas extending
an ambient frame. Published persistent forks retain their index; only admitted
class and occurrence changes are propagated.

The framing regression inspects the actual opened context returned by
`call_kept_ownership`, rather than relying on a successful general permission
check, so it detects a missing graph payload through `a = b = c`. Controls cover sibling isolation and retained source authority.
Additional tests cover late equalities, insertion/consumption deltas, preserved
parent states, and fresh plus framing construction beside 16, 64, 256, and
1,024 unrelated resources and equality facts. Both deterministic query work and
persistent-map work are measured, so deferred publication or a hidden ambient
scan cannot pass merely because the final lookup is cheap.

Publication alone does not complete candidate selection: the consumer
interfaces above establish bounded selection and refusal.

## Checked pointer-read sources

Typed pointer-read producers share `PureFactContext::register_pointer_read`.
It records the existing value's load definition and, when the exact defining
state (or its recorded canonical projection source) is a `CellsSeeded`
edge supplying the entire read footprint, admits equality with that run's
source read into the branch's graph. Only load-valued, contiguous, live slots
of the required width qualify. The check inspects the selected slots rather
than the run's span, address aliases, or state history. Canonical
projection bridges use exact producer registry entries. These are trusted
kernel rules; they introduce neither proposition premises nor access rights.

Ordinary pointer equality queries and resource consumers use the resulting
closure. A later integer address equality propagates through the registered source
applications without repeating this check. There is no special comparison
rule in `fold`. Producer publication occurs only after a typed read's existing
prerequisites have been checked. The graph's generation invalidates equality
misses recorded before publication; persistent sibling contexts retain their
own admitted unions.

Function-pointer reads retain the same structural loaded-pointer descriptor as
object-pointer reads, with the callback signature in the complete C value.
Their descriptor supplies the exact state and address without a scalar
variable or a defining equation. Nonvolatile statement reads from borrowed
callback tables also retain the checked current-cell equation. Statement
publication preserves that evidence in the successor's fact context; it grants
neither an ordinary proposition premise nor access to memory. Volatile reads
remain outside this bridge.

[`function_pointer_read_uses_checked_table_alias.md`](https://github.com/clicklang/click/blob/master/mdtests/function_pointer_read_uses_checked_table_alias.md)
checks a complete callback-field copy through a proved constant-table alias;
its missing-alias counterpart is refused. Kernel tests cover checked statement
publication, redundant producer equations, sibling isolation, missing premises,
changed sources, and absence of additional read permission. Predicate and callback lookup consume these checked pointer classes through
the shared buckets described above; no additional transport proof is needed
when the predicate's other arguments match.

The same producer boundary handles one immediate `Store` edge. It uses
structural object separation or an exact constant byte gap, after re-expressing
the selected read in the store's block through established graph equality.
It checks the store's full value width against the read footprint and admits
`load(after, address) == load(before, address)` only when their bytes are
separate. The exact byte geometry is shared with the memory checker. It does
not use address inequality alone, scan ownership frames, or walk older memory.
Already admitted single-store edges compose through ordinary graph closure;
unknown store-address aliases require a later producer check once the needed
separation is available. Unregistered intermediate edges remain unknown.

Memory state producers also maintain an immutable **read identity** for graph
load congruence. A recorded `CellsForgotten` edge inherits its base's identity:
removing cached knowledge changes no program bytes. A load-valued `CellsSeeded`
run inherits it only when the run's source and base already share that identity
and each slot's stride equals its value width. Copying the same bytes already
in the base is materialization, including successive sibling runs copied from
an equivalent earlier state. Other transitions receive a distinct identity.
The pointer and int32 graph-load signatures use this key while the existing
load terms and C pointer values retain their original state representation.

This metadata is part of the trusted kernel and establishes value equality
only. It does not establish state equality, read permission, initialization,
allocation continuity, or framing. Unrecorded pruning, constant or symbolic
storage runs, changed sources, stores, and havoc cannot inherit a key by this
rule. Checked separate-store unions still belong to their proof branch.

The key is fixed at first interning. If a state was already interned without
this annotation, recording a later edge conservatively loses the new equality;
existing graph applications never require relabeling or rescanning. Arena reset
keeps prior-session keys distinct. Production uses immediate-source key lookups
and does not enumerate slots or registered reads. Endpoint queries compose
arbitrarily many already-produced materialization/forgetting transitions with
ordinary congruence, without intermediate read publication or a history walk.
Deterministic regressions check approximately linear production over increasing
histories and constant endpoint-query work.

The recursive unfold → sibling-field write → refold fixture verifies,
expands, and independently rechecks. Overwriting the pointer field instead
rejects the expanded proof.

A load's equal-cell scan also reads this graph when the cached cells are a
seeded run. A run names the slot a load is at from the byte shift between the
load and the run's base. `run_slots_equal_to_load` re-expresses a load expressed
in another block in the run's block
with `pointer_in_block`, one keyed query over the affine class relation, so a
run answers for `id + 8` exactly as a single cached cell does through
`pointers_known_equal`. It selects a cached slot only; it adds no separation,
framing, or read authority: the slot is the one a load expressed at the run's
own address reads from the same state. `mdtests/fold_at_arm_identity_after_store_to_other_node.md`
and its three negatives retain the case.

A retained cell-map entry alone is insufficient preservation evidence:
low-level state construction can leave it present after a write through a
possibly aliasing address. Other memory transitions and separation forms
remain future work at this common kernel boundary. Deterministic tests cover
late read-address aliases and transitivity, complete and incomplete footprints,
changed and unknown writes, branch isolation, increasing runs and alias
classes, constant work beside increasing unregistered store histories, and
approximately linear composition of published store edges. The ordinary
single-store Click claim expands and independently rechecks; changing its C
write to overwrite the pointer field rejects the expanded proof.

## Persistence and cost

Follow the [verification-efficiency contract](verification-efficiency.md):
explicit checking is approximately linear up to logarithmic indexing factors
in the selected source, proof, and required output. Incremental closure is a
proposed means to meet that contract, not a blanket complexity guarantee.

In particular, measure signature maintenance, persistent map updates, affine
payloads, explanation construction, resource reindexing, and repeated branch
extensions. Do not claim a whole-verifier bound from union-by-size alone.
Avoid whole-state clones, deep structural cache keys, repeated same-state
load scans, and alias enumeration on each resource access.

Restricted contexts rebuild from the selected premises and required term DAG.
They must not inherit ambient merges or explanations. Contexts never withdraw
a fact: a branch forks the persistent parent, so no consequence needs
invalidating. Execution writes do not remove facts about old states.

Deterministic regressions vary multiple input sizes along these axes:

- chains, balanced merges, late merges, and repeated equality queries;
- nested loads and many unrelated loads within one state;
- repeated loads across a growing store history;
- resource lookup through growing classes and resources present before merges;
- many branches extending a large common prefix; and
- restricted contexts beside growing unrelated ambient facts.

Count total work as well as query work so moving a scan from query to insertion
does not hide it. Ordinary verification must pass before profiling or expansion.

## Evidence and trust

The closure is a kernel decision procedure. Every non-definitional merge must
have a checked source: an admitted hypothesis, an execution rule, another
checked derivation, or a congruence/theory consequence of such sources.
Certificates and selected-premise tactics must use only their allowed context.
The graph itself is trusted; a kernel equality query does not require a
separate explanation or derivation checker. A future explanation facility
would need a concrete consumer, such as diagnostics or premise dependency
reporting. It is not a prerequisite for `click expand`: a simple checked
operation can query the graph maintained from the certificate's allowed facts.

Equality substitution has a kernel-owned checked rule in
`proof/equality_rewrite.rs`. It admits the cited equality through the persistent
exact premise index, computes the substitution, and returns a private checked
result. That result constructs the proposition obligation. A Surface
spelling must lower to the checked result with the same read identities,
subject to the kernel's exact observation and Integer normal forms. A detached
scalar read can use the indexed store name for its exact snapshot, address,
and type. The candidate helper used by smart planning has no proof authority.

The outer quantifier walk refuses binder collisions with the bounded,
carrier-aware variable collector, which treats states as opaque. Direct
regressions cover unavailable/reversed premises, sibling-context isolation,
forged presentation, shadowing, capture, and ambient premise/state scaling.
Goal lowering/unfolding and other transitions through the generic publisher
are separate trust boundaries.

Soundness tests include unproved aliases, state changes, incompatible load
interpretations, branch leakage, restricted-premise leakage, offset wrapping,
and tampered equality explanations. Constructor injectivity and no-confusion
are class rules (see "Typed algebraic model values"); cyclic constructor
equations remain unrefuted. Distinct constants of the same sort produce a contradiction;
constants in different sorts must not be merged at all.

## Admitted inputs and separation indexes

The equality service owns both closure and exact admission inputs; there is no
parallel equality-class engine. `PureFactContext` keeps the propositions a
proof holds; its equality consumers delegate to `EqualityGraph` for Boolean
queries, source enumeration, premise paths, and constant discovery. Broader
theory and tactic extensions require a concrete use case.

`equality_graph/admitted.rs` documents the retained input selectors. Exact
pointer/offset endpoints, full-width source neighbors, literal-pinning
premises, algebraic constructor-field projections, typed read definitions,
alignment premises, and canonical edge support counts belong to this service.
They retain source forms and proof premises; they do not maintain a second
notion of equivalence. Their owning allocation is shared until the first input
mutation. Its private erased handle also breaks the recursive Rust `Send`/`Sync`
type path through resource indexes retaining a graph and source propositions
retaining memory/proof contexts; typed access never changes the stored input
type. In particular, an exact one-hop source query must not
silently substitute an inferred congruence equality in a certificate requiring
a written premise. Scalar premise paths use incrementally filed source edges
rather than a lazy scan of all conditions. Full-width load-source transport
selects the exact address/interpretation bucket before comparing states.

Literal values and conditional/load witnesses are annotations of shared term
roots. Folding uses application dependency hooks and reindexes affected uses
when a class learns a literal. Ordinary integer operators use those same applications for nonliteral
congruence, with typed curried applications for the remaining conversions and
wide operators. Full-width constant discovery first asks the shared class engine;
contextual folding and implicit consulted-premise collection retain exact source
premises. None of these operations grants memory access or state transport.

Restriction resets the closure and refiles only the selected facts. Branch clones
share persistent input roots and fork subsequent changes. Pointer-predicate source handles are retained with
the service so reconstruction cannot import facts from a sibling context.
Atomic condition matching checks only the selected forms for full-width
sources. Parameter-store shortcuts consult selected coordinate dependencies.
An admitted read equality records its written coordinate variables without
inspecting the values cached in its memory state. There is no global read/state
dependency flag: unrelated read, scalar, or offset premises do not disable the
shortcut. A source mentioning the selected coordinate, or a read in the selected
offset itself, still uses ordinary store reasoning. Atomic parameter bases also
exclude registered loaded-pointer variables. The alias and ownership checks are
unchanged.

`unrelated_read_inputs_preserve_the_selected_parameter_partition` checks fixed
query work as unrelated read facts grow, with controls for a relevant equality,
a read-valued offset, and sibling-context isolation.
`sequential_owned_parameter_stores_ignore_earlier_cached_fields` checks bounded
per-store work beside growing scalar/pointer cells with an unrelated read fact;
`a_cached_parameter_partition_does_not_hide_aliases_or_wide_cells` also checks
that explicit read equations connecting parameter coordinates invalidate aliases.

Memory authorization, contextual
state reasoning, and explicit tactic search remain separate judgments with
their own contracts; they are not alternate stores answering value equality.
Scaling regressions cover selected source enumeration, long constant chains,
range-value equality, missing premises, and unrelated ambient facts. Gate and nightly
validation remain required evidence for changes to this representation.

Complete pointer comparisons retain their common base rather than becoming
bare offset comparisons. The pointer disequality dispatcher reads the stated
nonempty-range separation index for that form too. Common-block anchors use
the existing offset-pair key; different symbolic blocks use a complete-pointer
pair key, since separating different objects does not distinguish their
numerical offsets. Both indexes retain the exact source proposition and track
its insertion and restriction. Empty or unresolved
ranges add no anchor evidence. C condition decisions and proof-side known-fact
lookup (including `close()`) share this indexed rule. The latter also
handles negated pointer equality and retains the exact separation premise;
it performs no owned-composition scan, alias search, or unfolding.

Store framing also retrieves stated separation authority through the checked
address classes of both range anchors. `SeparatedAddressIndex` retains each
exact proposition and follows term-class merge deltas, rekeying only incident
pairs. Persistent roots and separate cache locks preserve context forks. The existing direct anchor lookup stays first. Every retrieved
candidate still needs membership evidence covering both complete byte ranges,
and an overlapping numeric address relation rejects the frame.

### Resource logical call and constructor domains

Opening an active selected resource body retains the nominal pointer domains of
its logical calls and algebraic constructor fields as explicit
`object_type[T](pointer)` facts, written `is_a<T>(pointer)` in Surface. These facts
use the existing supported pointer-type buckets and their ordinary scope
rules. They are produced along the selected lowering path, rather
than recovered from annotations in opaque interned call arguments. An inactive
body exports none. Folding uses ordinary lowering: it must establish every
nominal call or constructor field domain before the proposed resource can be
constructed. Incompatible positive pointer evidence is never replaced. Merely
naming a struct pointer parameter in an empty resource supplies no evidence.

The executable controls are `model_pointer_resource_call_domains.md`,
`model_pointer_resource_fold_requires_call_domains.md`,
`model_pointer_empty_resource_does_not_type_parameter.md`, and
`model_pointer_resource_inactive_call_domains.md` in `mdtests/`.
`held_resource_constructor_pointer_domain.md` checks unfolding and refolding
a constructor-bearing fact; kernel controls check missing and incompatible
evidence.

Complete C pointer-to-integer copies retain nominal type receipts in the
`PointerInteger` representation record. A numeric `IntegerAddress` observation
retains access-class annotation only: its annotation is excluded from numeric
identity and cannot establish nominal type evidence. Recovering a typed pointer
from those coordinates still needs the current scope's checked type facts.
This does not recover a provenance, bounds, or memory permission from numbers.

### Numeric coordinates of logical word casts

A logical word cast names its address as `$integer-address(bits)`. Registering
that constructor joins its numeric address to `bits` in the uint64 classes,
using the existing iterative dependency worklist once per constructor. Byte
displacements and compatible same-state reads therefore use the same
classes as the original word. Complete pointer-value applications use the numeric
address as one operand, alongside independent provenance and bounds operands;
integer address equality cannot merge those other operands. Complete-value comparisons whose provenance and
bounds already match reduce the remaining zero-offset constructor comparison to
uint64 equality. The internal constructor does not enter the result-domain
congruence used for actual pointer-returning pure functions. Numeric definitions
alone establish no provenance, bounds, object type, or memory authority.
The explicit source control is `tagged_pointer_explicit_round_trip.md`; branch
scope, displaced addresses, state distinctions, and provenance
separation are covered by the equality-graph unit tests.
