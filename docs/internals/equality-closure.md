# Equality closure design

Status: bounded resource lookup migration complete, 2026-10-02. The trusted persistent graph
maintains affine pointer classes, offset and int32 congruence, and registered
same-snapshot pointer, four-byte scalar, and complete eight-byte scalar loads. Selected normalization,
transport, memory, resource-value, and range consumers query it. Ordinary C
pointer loads still have a storage-relative representation; equality-aware
resource indexing is implemented for selected consumers. Other theories
described here remain possible future work.
The seven resource lookup cleanup milestones are complete. The rbtree proof
has its own remaining frontier; completing it is not an additional equality
migration requirement. Wider theories in this note remain reference material,
not new P1 acceptance criteria.

## Shared typed pointer reads

A registered typed pointer read is a congruence application of its snapshot
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
no read authority, initialization, allocation identity, or cross-snapshot
frame proof. Snapshot read identities retain their existing independently
checked representation-only normalization.

Immutable definitions and checked read evidence serve different purposes.
An existing C value can keep its original load definition when a later read
returns it from a cached cell. A checked resource-index evaluation retains
that later snapshot and selected address in its certified producer binding.
After its prerequisites pass, it admits `value == Read(snapshot, address)`
through the graph's existing checked-equality input. It does not mutate the
value's definition or install a global observation. The input is branch-local
and retained by input checkpoints; rebuilding a context without its evidence drops it.
Offset equality queries register the same producer-retained typed-read
definitions as full-pointer queries. Registration visits only the selected
operands; it never infers pointer-block identity from equal offsets.

A checked pointer store also emits the equation between its stored pointer
address and the address returned by the typed pointer read at the written
cell in the resulting snapshot.
The equation travels with the certified execution facts into the ordinary
graph, so an equal-address query does not require a preliminary read through
the store spelling. It relates only that snapshot; a subsequent write needs
its own preservation evidence. Scalar or partial stores do not emit these
pointer-address equations. The equation does not equate designations;
designation transport requires the complete checked pointer carrier.

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
Compound pointer and offset queries retain the generation at which their read
dependencies were registered. Repeated queries reuse that result; a newly registered logical
read definition changes the generation and invalidates earlier misses. This
cache retains term dependencies only, never a successful equality judgment.

Ordinary and volatile program reads do not use this resource-index admission
path. Other producer migrations and removal of older consumer recovery rules
remain separate work; this first change does not claim universal read adoption.

## Shared 64-bit expression congruence

`add_uint64_equality` admits checked 64-bit equalities into the same persistent
term classes; `are_uint64_equal` queries their closure. UInt64 addition,
subtraction, multiplication, division, remainder, and bitwise AND/OR/XOR are
congruence applications, with distinct operator tags. Pointer-to-word address
expressions use the complete pointer address class. No cancellation,
injectivity, arithmetic definedness, or memory access permission follows.
Unsupported constructors remain opaque.

A `Bits64` read uses its registered defining snapshot and complete address,
with an eight-byte producer-width check for named scalar reads. It is a
separate application sort from pointer reads and int32 values. Equal addresses
at that snapshot therefore produce equal words, and the ordinary parent-use
index propagates that equality through surrounding expressions. Different
snapshots are not unified by this registration; existing checked frame or
copy evidence must establish any cross-snapshot equality.

Exact wide premises are retained as counted, typed edges for withdrawal and
context rebuilding. Derived resource indexes receive them through the same
persistent input history. Ordinary condition and required-obligation checking
query this closure, including contexts that defer broader search. In
particular a fold needs no special rule to combine a read-address alias with
another pointer alias nested in a packed parent/color equation.

## Fact availability through congruence

`PureFactContext::contains_known` is the semantic lookup used by proof-fact
availability and `assumption`. Exact membership remains a separate operation
for premise admission, withdrawal, and provenance checks. Lookup first checks
the exact index, then asks the same scoped graph used by equality consumers.
It performs no unfolding or implication search.

Machine equality goals ask for class membership. Supported machine comparison
facts (including false conditions) have typed application signatures annotated with
their admitted truth value. A late operand equality updates those signatures
through the existing parent-use index; queries never scan ambient facts.

Machine-valued Click function applications also have congruence signatures.
Their argument list uses shallow binary application nodes, preserving function
identity, result width, argument order, C types, and array-reference snapshot
identity. Int32, UInt32, UInt64 and pointer arguments use the existing scalar
and complete-address classes. Other arguments, including binder-bearing
algebraic and mathematical Integer expressions, currently retain exact opaque
identity. Legacy applications without argument sorts also remain opaque. This
does not introduce injectivity, arithmetic solving, memory permissions, or
implicit equality between different snapshots.

Condition truth follows scoped persistent graph forks. Its exact support is
retained for rebuilding after withdrawal, replacement, or context restriction;
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
`are_offsets_equal` accept whole pointer-offset terms. Supported pointer-load
applications and offset terms register on demand during insertion and queries.
`add_int32_equality` and `are_int32_equal` admit and query explicit int32
equalities, addition congruence, and registered same-snapshot int32 load congruence. The uint64 interface above extends the same closure to wide reads and selected
wide expressions. Further sorts and consumers remain separate work. `pointer_is_classed` and `pointer_spellings` are explicitly
pointer-specific compatibility helpers for legacy consumers.

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
load interpretation, and memory snapshot of the query. Cloning shares
persistent storage while keeping subsequent additions branch-local.

The larger typed-pointer migration remains an unmerged historical reference
draft in `codex/egraph-foundation`; its behavior changes are not on `master`.

`normalize() using { ... }` queries this existing graph while reducing
pointer and int32 equality conditions, including guards of conditional expressions.
Successful queries replace equality conditions with true; unsuccessful queries
leave them unknown. The same traversal handles equality leaves and nested
conditions. Graph queries may use ambient graph facts; the `using` list
restricts the additional conditions used for reduction. All cited premises must still be available and
supported. Other ambient facts, quantified bodies, and cross-snapshot frame
search remain outside this operation. Expansion retains the simple step and
rechecks it in the same proof context, without an explanation API or a
per-tactic graph rebuild. Restricted `simp() using` planning checks a
normalization candidate against only its selected context before emitting the
simple step; omitted ambient equalities do not participate in that search.
Explicit pointer-offset equalities also enter the
same graph and are available to this normalization check. This covers ordinary
C pointer parameters, which lower to offsets in a shared block, without
changing their representation.

The offset fragment interns whole terms with shallow keys and uses persistent
union-find weighted by members and parent uses. Its query first recognizes
exact affine-equivalent byte offsets, including regrouped or reordered sums
without a premise. `simp` uses that query for same-block pointer conditions,
which lower to offset equality. Addition signatures identify operand classes,
so equal operands establish equal sums. Indexed parent uses
propagate late merges through nested additions with an iterative worklist;
parents of the lighter class are revisited. When a class first acquires a
literal value, its existing parents also receive constant evaluation. It preserves widths,
signedness, and machine-term snapshot identity, and adds no arithmetic solver
or cancellation rule. Queries and additions use indexed access. Existing
context restriction and equality-withdrawal rebuilds retain all graph
fragments from their remaining exact equality indexes. The pointer query
compares affine coordinates and whole offset classes inside the graph. Same-block pointer premises also join whole offsets.
Equal-base and representable constant-displacement queries use direct offset
class lookups, including either translated spelling. At an unclassed ordinary
base with no offset merges, the known-equality query stops after reflexivity;
explicit offset normalization remains available through `are_offsets_equal`.
This avoids normalization work during unrelated field-separation checks.
These checks require no alias enumeration or cancellation rule.

Checked cross-block pointer premises involving the shared external-argument
block, concrete storage, or an unspellable displacement also join their raw
`address(block, offset)` applications. An address class retains one offset
witness per exact block. Merging classes with a shared block joins those
offsets: `address(A, x) == p` and `p == address(A, y)` establish `x == y`,
regardless of the affine representative. This is exact byte-address
injectivity within one block; addresses from different blocks do not imply
equal offsets. Only witnesses in the lighter class move, so unrelated
address classes are never scanned. Offset-class merges then propagate by
ordinary congruence, so `x == y`, `address(A, y) == z`, and `z == null` establish
`address(A, x) == null` in any insertion order. Affine block merges translate
registered applications when that translation is spellable. Query registration
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
address spelling retains its registered shift definition, so repeated queries
do not repeat base registration or closure. This supplies address equality only: field access still requires an owned range of the correct
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
memory snapshots. Int32 scaling is a congruent application: equal indices
with the same byte width give equal offsets, and existing offset addition
applications propagate that equality. Parent-use indexes handle late scalar
merges in the same worklist. Literal indices join their folded byte constants
when multiplication fits i64. This does not infer congruence for unsupported scalar operations,
64-bit or mathematical-integer equality, or general injectivity of offset constructors. Exact scalar premises are counted under shallow canonical edge keys so
withdrawal preserves other premises that support the same edge. `MemoryLoad`
expressions are not separately interned for support tracking: that would allow
cross-arena snapshot comparisons to traverse unrelated memory. This is an
additive consumer migration.

True offset premises also feed the shared graph through the existing checked
int32 element-index interpretation: four-byte scaling, aligned constants, and
supported additions. Equal byte offsets then imply equal int32 index residues.
This premise translation shares support counting with explicit scalar edges;
withdrawing one premise retains any other support for that edge. It does not
infer exact offset equality from equal wrapping residues.

`PureFactContext::int32_values_known_equal(left, right)` is the shared query
for wrapping int32 value equality in the trusted graph. It replaces the old
Boolean fact-component walk and its separate memo. Condition decisions,
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
stored term. The general memory and expression reasoning APIs still perform
their explicit checked judgments; the known-value query does no arithmetic
search or snapshot transport.

The lazy exact-equality index remains for consumers that enumerate aliases or
produce premise-path evidence. Those are distinct operations, not a second
Boolean equality checker. This chunk does not migrate the 64-bit adjacency
index, mathematical-integer equality, or constant discovery.

Wide-read alias checks retain the latest producer observation for each load
identity in the current function epoch. Assigning a load identity, including a
cache hit, records its complete live snapshot and address. Two model match arms
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

The central memory resolver now asks pointer classes for cross-block equality
and offset classes for exact same-block byte-offset equality. Its pointer
query still rejects structurally distinct blocks and explicitly separated
ranges; its offset query still treats equal wrapping int32 residues as
insufficient unless the existing exact-index rebuild check succeeds. A graph
offset edge can flow
through int32 scaling and offset addition into a pointer address without
building the legacy scalar fact index. Context forks, fact withdrawal, and
restriction keep these answers scoped to their supporting premises. Broader
memory arithmetic and framing rules remain in the resolver.

The simple pointer-equality decision now uses typed graph queries only. It no
longer scans all ambient condition facts for a matching translated equality
or walks their alias component. Overflow-guarded translation such as
`p == arr + i` after incrementing `p` and `i` instead uses an explicit
`arithmetic() using` proof with the entry pointer relation and strict index
bound. A displaced cross-block query now uses an exact translated offset edge
only for a representable constant base displacement. Symbolic displacements
can remain unknown until a checked proof supplies the translated equality.

The memory-separation reader uses the same known-equality query. The
superseded Boolean alias-component walk has been deleted. Exact alias indexes
remain for evidence-producing enumeration and other consumers; their presence
does not imply a second Boolean pointer-equality system. Deterministic tests
cover mixed offset/block chains, all premise insertion orders, late offset
merges, branch isolation, and bounded query work beside growing offset classes.

The full and shallow `Bitvector32Equal` decisions use the shared known-value
query. Explicit negative premises, arithmetic rules, and checked memory
resolution remain separate. Int32 fact transport uses the same query before
its structural and broader expression rules; it has no separate Boolean
fact-path fallback. Exact pointer-offset decisions retain their no-wrap guard.

The commutative int32-addition matcher also queries the graph when comparing
individual addends. A reordered sum can therefore use registered load
congruence or a joined scalar class even though the graph does not itself
reorder addition. Other checked addend rules still cover forms outside this graph fragment.

Direct memory-resource matching now queries graph equality for its int32 range
start and end values through the shared known-value query. These fields are
scalar values, not byte-offset equivalences; the resource base still follows
its separate pointer check. Congruent sums and registered same-snapshot loads
can therefore identify equal range endpoints, while changed snapshots and
withdrawn premises remain distinct.

The checked `CValue::Int32` value comparison now queries the graph before its
broader memory-resolution path. Direct composite, token, and instance matching
use that shared typed rule for resource arguments and instance fields, rather
than maintaining a resource-specific graph check. Byte-typed values and pointer
arguments retain their separate rules. Registered loads in one snapshot may
match as values, while changed snapshots and withdrawn premises do not.
Multi-size regressions check that graph matches avoid building the legacy fact
index.

Contract certification's `Bitvector32Equal` check now uses this typed int32
value rule after its checked cross-snapshot load rule. Graph-congruent sums and
same-snapshot loads therefore certify without searching the legacy fact index;
changed snapshots and withdrawn premises still fail. This affects scalar
equality claims, not pointer-offset certification.

Certification of call- and loop-havoc mutable-range lists now uses the typed
int32 value rule for each start and end, after separate width and pointer-base
checks. The general range-endpoint helper also serves scaled pointer offsets;
it has not been changed to accept wrapping graph equality as exact address
equality. Regressions cover same-snapshot loads, changed snapshots, withdrawn
premises, width mismatch, and multi-size queries without the legacy fact index.

The structural, memory-resolution, and covering-span loadable-range readers
now share one typed int32 value rule for matching byte extents at the same
base. Their callers retain the range-availability check for the goal snapshot;
equal extents do not supply viewability by themselves. Tests retain the
loadable-premise and base boundaries and check direct multi-size queries
without the legacy fact index.

Same-base range containment now uses the typed int32 value rule when its
signed endpoint-order check has equal operands. Equal endpoint bitpatterns
establish `<=`; this does not infer an exact byte-offset difference from a
wrapping scalar equality. Other order and containment rules remain separate.

When a signed-order fact is found by one exact endpoint, its other int32
endpoint is compared through the graph first. The containment order check
tries these indexed facts before its broader scalar equality fallback, so a
graph-congruent match does not build the legacy fact-path index. Candidate
lookup still requires one syntactic or canonical endpoint key; it does not
search every order fact for a graph-equivalent endpoint.

The kernel comparison of condition facts for certified transport now uses the
typed int32 value rule for operands of matching signed-order or equality
conditions. Condition kind and truth value must still match. Registered loads
remain scoped to their defining snapshot, and withdrawn premises lose their
consequences. Multi-size queries avoid the legacy fact index.

Allocation continuity across a call now compares its two 32-bit size values
through the typed graph rule after the separate allocation-base check. This
does not use wrapping value equality to establish pointer-base equality.
Regressions cover same-snapshot loads, overwrite and withdrawal boundaries,
different bases, and multi-size graph queries without the legacy fact index.

After indexed resource matching misses, the zero-ownership fallback now uses
the typed int32 graph rule for the required quantity. This is value equality
with zero, not a resource-key or pointer match. Regressions cover graph-
congruent registered loads, changed snapshots, withdrawn premises, and
multi-size zero-quantity queries without the legacy fact index.

For a range pair already selected for composition, endpoint comparison uses
the graph-backed int32 condition decision. The composition helper no longer
repeats a separate legacy fact-path walk after that decision. Candidate
selection remains its own index boundary: normalization does not yet discover
every pair whose endpoints become equal only through graph congruence.

After the existing memory resolver establishes a four-byte scalar load's
value, load equality compares it through the shared int32 query. Resolution still supplies the value in the
load's snapshot; graph equality neither resolves stores nor grants read or
frame permission. Other load widths keep their existing comparison path.
Regressions cover both comparison directions, a changed snapshot, withdrawn
premises, a one-byte load, and multi-size query work.

When both operands are resolved four-byte loads, the same path compares their
checked stored values through the same graph query. Neither load's opaque name needs to equal the other load's stored term.
Each value still comes from its own recorded snapshot. Changed or withdrawn
evidence and a resolved one-byte read do not use this two-load rule.

Registered four-byte scalar loads also participate as int32 applications. Their
signature contains the registered defining snapshot's arena identity, the exact
storage block, and the offset class. Equal offsets therefore give equal reads
in that snapshot, including when the offset equality arrives later. Load
registration follows nested index dependencies iteratively; merge propagation
uses the same parent-use index as addition and scaling. Neither step scans
unrelated snapshots or enumerates address spellings.

The defining snapshot can already be an assumption-free canonical projection.
The graph uses that registered definition, never the mutable live origin. It
does not equate distinct defining snapshots or storage blocks, search for frame
evidence, resolve stores, or grant read permission. Unregistered, unknown-width,
and other-width loads remain opaque. Existing canonicalization can independently
retain a value across a justified memory change; this slice adds no new rule
for doing so. Global load naming remains independent of contextual equality.

Checked transport conclusions enter the ordinary int32 equality interface.
For example, after a store to `p[k]`, explicit transport can use `i != k` to
prove that `p[i]` equals its entry value. With `i == j`, normalization then
combines this edge with current-snapshot load congruence to prove the same for
`p[j]`. The graph needs no frame search or snapshot-merging operation.
[The executable composition example](https://github.com/clicklang/click/blob/master/mdtests/normalize_using_transported_int32_loads.md)
keeps the transport and graph steps explicit. Regression tests remove either
premise or the bridge, reject an overlapping store, recheck expansion, and
verify that withdrawing the bridge removes only its cross-snapshot consequences.

## Problem and scope

A proved equality must have the same meaning at every kernel consumer.
Currently facts, cells, and loads are indexed under particular spellings, and
consumers recover different subsets of the known equalities through alias
retries, graph walks, or local normalization. The rbtree insert proof exposed
this at read permission, fold body facts, ownership consumption, and loads
after stores. Local repairs now cover some fixtures but do not establish the
general invariant.

Build one persistent equality service in the kernel, using congruence closure
without saturation. Hypotheses, checked proof steps, and execution contribute
equalities; congruence propagates them through registered applications. The
service does not invent rewrite rules or search arithmetic identities.

The first complete fragment is pointers and typed loads. Bitvector/integer
applications, algebraic constructors, and pure-function applications follow
as separately reviewed theory extensions. Ordering, general arithmetic, and
cross-snapshot frame derivation remain outside the closure. A checked theorem
from one of those procedures can contribute an equality to it.

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
value independently of the storage address spelling and pointee width. The
graph can answer equality of two such applications without replacing the
`Pointer` values produced by C execution. A live caller must supply the actual
defining snapshot and address from a typed load site or checked evidence; the
storage-relative `Pointer::as_loaded` shape also describes indexed pointer
arithmetic and is not sufficient evidence by itself.

The bridge from a completed nonvolatile C pointer read to the graph
application is execution evidence scoped to that path. The typed producer
registers its value with the exact defining snapshot and address; only a
matching defining equation in the path's fact context files the equality in
the graph. It is not published as an ordinary proposition premise: doing so
changes a statement theorem from `Executes` to `bridge => Executes` and makes
resource child-argument checking reject previously readable expressions. The
graph relation changes neither logical premises nor read permission. Volatile
reads do not register this bridge.

Specification pointer loads now retain an exact definition supplied by their
typed producer as graph term metadata. Resource-entry cells and lazy cell
ranges use the same typed constructor and retain this definition before any C
access, so a later read through a model alias has the same identity even at a
nonzero field offset. These definitions are shared across
contexts within one verification session, like load-variable interning;
address hypotheses, unions, and their consequences remain in persistent
path-local graph roots. Reconstructing a context must not forget what a logical
term denotes. Registration never decodes arbitrary pointer arithmetic and adds
no proposition premise, ownership, read validity, or cross-snapshot equality.
Each query registers only its named values and their recorded dependencies.
Filing a checked pointer equality also registers the producer definitions of
its two operands. A later query can therefore use a read hidden behind another
class member without first comparing that read directly or searching the
class for read spellings.
A registration generation distinguishes reasoning memo entries from earlier
misses, without scanning or rebuilding the proof environment. `simp` can emit
`normalize() using {}` to check an equality against this ambient graph.
The nonrecursive `mdtests/egraph_resource_pointer_load_alias.md` regression
checks this after an unfold publishes address equality.

An explicit pointer rewrite uses this producer metadata to distinguish a
pointer-valued read from ordinary address arithmetic. For a registered read,
it rewrites the defining address at the read's original snapshot and names
that rewritten read. It does not add the owner's alias displacement to the
loaded value. Resolving the new address against the original snapshot keeps
cached child identities across a joined loop; a projection for the old address
alone is insufficient. Naming uses exact recorded reads and cached pointer
cells; a cold read keeps its snapshot application without searching history.
A complete pointer value cached at the rewritten address is returned directly
from that snapshot, including after a pointer store.
The joined-pointer-field fixtures cover the explicit
rewrite and rejection of an equality about a different field.

Recursive resource child indices use the same term-definition interface.
After a child expression passes the existing readable-expression and argument
checks, its certified typed producer metadata is retained before the temporary
fact stream is discarded. The cached scalar-cell conversion preserves this
metadata just as the symbolic pointer-read route does. Ordinary propositions
and volatile reads cannot supply it. `mdtests/egraph_recursive_child_alias.md`
checks unfold and refold at the same complete parent carrier while retaining
an identical model, without intermediate field-load claims or C writes. The
model's pointer identity can be numerically equal to the parent address without
sharing its designation; that equality cannot authenticate a refold at the
model pointer. The original model-pointer refolds remain negative regressions.
This does not transport loads across different snapshots.


The kernel now has a distinct `PointerLoadId`, `PointerBlock::LoadedPointer`,
and a constructor/decoder pair for `(defining snapshot, address, displacement)`.
The equality graph indexes this explicit pointer application without consulting
the scalar load registry's mutable access width. Ordinary C pointer-load
producers still create the storage-relative form; their checked path-context
bridges relate that form to the explicit graph term. Making the explicit name
the execution value is a separate proposal that would require a coherent
review of materialization, substitution, provenance, and rendering. Merely
swapping the constructor breaks existing verification and expansion fixtures.

The existing weighted pointer classes are useful groundwork:
`base(member) = base(representative) + delta`. Exact affine normalization can
relate displaced spellings such as `p + 8` and `(p + 4) + 4`. Preserve signedness,
bit width, wrapping, and definedness obligations of the supported C semantics;
do not distribute arithmetic through a wrapped index as if it were an
unbounded integer.

The graph now records an exact offset equality when a congruence merge joins
two pointers already in one block class. Further changes to offset-atom
classes still need a reviewed notification path into application and resource
indexes. Account for affine expression size when describing merge cost.

### Loads and memory snapshots

Model a load as an application keyed by its snapshot, address, and access
interpretation (sort/width and any other distinctions required by memory
semantics). Existing external registries may supply this information during
migration; the semantic key must be explicit in the design.

The typed graph query uses a distinct pointer-load name and an explicit
loaded-pointer block variant, rather than hiding another sort in the scalar
load-variable range. Its key is the assumption-free canonical snapshot,
address, and pointer interpretation (object-pointer value, eight-byte access).
Pointee type remains on the C value and is not key material. Live origin/epoch
metadata is separate from that defining key. The old widthless scalar load
registry can remain during this pointer phase; its mutable maximum-width field
must not decide membership in the new pointer-load application index.

Do not emit a scalar equality between a pointer-load name and a widthless
`MemoryLoad`. The pointer registry defines the graph application;
scalar bit views need their own checked conversion. A materialized pointer cell
already contains its value: reuse that value, including a retained value across
havoc only through the existing checked retention rule. If a future change
uses the graph's explicit loaded-pointer node as the C execution value, its
constructor, decoder, substitution, provenance, and rendering consumers must
be reviewed together. The current equality query requires none of that.

Equal addresses at one snapshot imply equal compatible loads. This must hold
whether the loads were registered before or after the address equality, and
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

Different snapshots do not become equal merely because addresses match.
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

Do not infer a pointer's provenance from the spelling of the cell that held
it. Do not infer an allocation's birth from a contract allocation claim or
from absence in a projected snapshot. The existing special rules for hidden
locals and later-declared locals need their exact preconditions retained.
Any broader rule needs its own positive and negative tests.

Snapshots form a DAG. A proposed class attribute such as "earliest birth"
needs a semantic ordering and evidence valid in the current path; snapshot IDs
or unrelated branch timestamps do not provide that ordering. Representation
migration is not authorization to add an unreviewed provenance theory.

## Incremental closure and indexing

Maintain an application-signature table and parent-use lists alongside the
persistent equivalence relation. When child classes merge, reconsider affected
parent applications, merge signature collisions, and continue until the pending
work is complete. Queries may register their explicit terms, but must observe
a closed state before returning. Batching is allowed only if it preserves this
boundary and charges the actual maintenance work.

The initial `PointerClasses::normal` recursively normalized loads with a depth
cap and a same-snapshot scan. It has been replaced. `PointerClassState` stores
load applications, block use lists, application signatures, and reverse
signature bindings. Registration walks only a query's unregistered load-address
dependencies; merges reindex users of moved blocks and enqueue colliding load
values for merging. Every registration/merge drains the worklist before return.
Class weight counts blocks and application uses, so high-fanout classes remain
on the heavy side of a merge. A context clone copies persistent roots into its
own lock; query registration cannot mutate a sibling's closure.

Signature keys contain snapshot arena identity, representative block identity,
and an affine-offset ID. Offset sequences are interned with shallow prefix keys
and retained machine-atom IDs. This removes deep snapshot/term comparison from
signature lookup. Explicit affine syntax is normalized with an iterative walk;
legacy spelling output sorts structurally rather than by interning order.
The existing weighted affine payload operations still need broader scaling
review for growing symbolic deltas. Same-block equations and equality between
offset atoms are not yet incorporated into this closure.

Registered pointer-width loads in opaque symbolic-block form enter this
application index. Ordinary C load construction retains its existing encoding;
checked read-site equations connect its values to the graph's applications.
Pointer comparison uses that closure directly. Read/fold resource indexing
has its own ownership and range-coverage boundaries below.

Resource lookup now pairs persistent resource roots with the trusted graph's
pointer-class merge stream. Memory facts have a raw block/affine-base index
maintained at insertion and removal, so a cold lookup can pair that index
without scanning the resource store. The initial execution proof boundary
registers the selected resource input's starts as typed graph address
applications. Successors register only newly published occurrences. A paired snapshot retains both resource and graph checkpoints;
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
pointer spellings. A selected candidate can express the requirement in its
own block coordinates using the graph's affine relation; this visits no other
class members. Existing local range matching remains responsible for
same-block containment and endpoint reasoning. Specification reads also use
the paired index for concrete affine addresses in classes whose memory entries
all have positive concrete read cores. A persistent AVL interval tree stores
each occurrence's byte start/end and each subtree's maximum end. It lazily
selects ranges covering the access's candidate footprint, including mixed extents and overlapping
views where the nearest predecessor is too short. A read stops at the first
candidate accepted by the ordinary permission and bounds checks; it does not
materialize every overlapping view. Updates copy only the affected tree path,
and class merges shift only the smaller resource payload's interval tree.
The occurrence count detects incomplete index coverage. A miss is final for
a complete concrete fragment; incomplete fragments use the bounded candidate
classifier described below. Positive hits retain their suppliers even when
coverage is incomplete. Neither case scans unrelated resources, including
resources published before a later address equality.
Whole-cell read hits also use an exact-start payload attached to typed graph
address classes. Offset congruence and late same-snapshot loaded-pointer
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
contributes its complete physical footprint,
and merges move both indexes from the smaller occurrence payload. Input
registration still belongs to the execution proof boundary. An unbound class
is unknown: scalar arithmetic or snapshot transport may justify an equality
outside this closure, but permission lookup cannot search for that evidence.
Candidate delivery is lazy; equality selects the
occurrence's own start and the ordinary checker still validates its quantity,
access mode, and bounds. Pointer reads require all eight bytes under the pinned
ABI, regardless of whether the resource counts bytes or four-byte elements.
Interior reads of longer ranges use the range checker. Unrelated scalar
equality no longer disables this cell
fragment. The same address payload supplies fold candidates, whose coverage
and consumption checks remain authoritative. Cold lookups cannot trigger full
input registration; the shared classifier uses retained evidence or refuses
unprepared selection. A proof boundary establishes input publication. Branches inherit registered
persistent roots. Pairing now keys cached views by the persistent history of
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
occurrence can therefore use that snapshot, including in a preexisting
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
consumers do not supply an alternate query spelling or reconstruct a range.
The direct ownership-support consumer uses the same retained alignment, then
restores the requested range's base from its checked start displacement. It
never asks an ambient graph that may lack the selected loads' registrations.
Whole-cell alignment checks the query against the occurrence's start in the
trusted graph. Interval alignment uses the checked affine block relation.
Neither path grants authority: the ordinary permission, width, and containment
judgments still decide whether the selected occurrence supplies the access.

Interval completeness is local to the registered affine address block class.
The graph maintains whether non-affine offset equivalences reach that class
through registered application dependencies. Unrelated scalar aliases no
longer disable concrete interval queries. This metadata is persistent, follows
late merges and block relabels, and applies to subsequently registered parents.
Affected classes report unknown coverage; exact whole-cell evidence remains
usable independently. Concrete loaded pointers use the interval contract after their retained
definitions register; there is no blanket exclusion of loaded-pointer blocks. An unpublished
loaded-pointer interval remains unknown: its raw structural root has not
registered all suppliers' retained origins, and a simple query cannot do that
whole-input work. Publication establishes this fragment's completeness.
Producer metadata indexes the read atoms in kernel-minted storage-relative
names, so a shifted expression registers its original defining read directly.
Exact address evidence therefore applies to shifted names too. Storage-relative
names whose affine coordinates remain symbolic still report unknown interval
coverage; that belongs to the symbolic containment milestone.

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
Candidate footprint calculation uses the complete physical access width. An
eight-byte pointer read requires all eight bytes, including when its supplier
counts four-byte elements. Candidate selection and the checked permission query
use the same footprint; a narrower logical field cannot authorize the read.
Deterministic regressions cover late aliases,
nonzero displacement, branch isolation, insertion/removal and normalization,
growing alias classes, disjoint spans sharing one base, concrete read hits and
misses, mixed extents, overlapping views, lazy delivery of covering ranges,
interval updates against an independent model, and incremental merges
with a large resource payload. Resource-section publication uses the expansion
delta rather than recreating views for unrelated ambient memory ranges.

Write-resource candidate selection now shares the complete affine interval
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
reverifies. Dropping the equality or either bound refuses the read. This
corrects context loss at the fold boundary; general permissions now share the
bounded supplier service below.
An indexed miss or failed candidate check is decisive for this covered
fragment; it does not retry spellings or scan the remaining resources.
Whole-cell writes additionally use a separate footprint payload containing
only positive concrete owners at registered typed address classes. Late
offset and loaded-pointer equalities update this payload through the graph's
existing merge stream. A selected occurrence supplies its own start address
for the authoritative range check. Views never enter the write payload; an
exact-size view cannot hide a larger owner. The read and write payloads share
the existing footprint/width eligibility rule and move only the smaller
occurrence payload on a class merge. Exact candidates do not depend on an
affine coordinate bucket. Unbound footprints and unsupported containment or
snapshot shapes proceed through the shared candidate classifier below; when
it cannot select a supplier, permission is refused. Unknown equality is not
disequality. Both access judgments require the complete physical width.
Input registration remains a
proof-boundary operation, not a scan performed by a cold lookup.

Address-class queries register the same retained logical-pointer definitions
as pointer-equality queries. Registration visits only the requested term and
its recorded producer dependencies, then closes them against the current
branch's equalities. A resource lookup therefore needs no preliminary equality
query to recognize `load(a)` and `load(b)` after proving `a = b`. It registers
no unrelated reads or resources and introduces no premise or access authority.
The regression asks the read and write indexes directly before any equality
warm-up, rejects sibling, displacement, width, and snapshot mismatches, and
checks cold address registration at multiple unrelated-definition counts.

Structural "already held" range checks no longer scan a pointer block's
resources. They use a publication-maintained index of base shapes and affine
origins, plus the raw interval summary for complete concrete coverage at a
plain origin with constant displacement. Updates and consumption maintain
persistent roots, and branch copies share them. The separate structural-read
permission API has been retired; reads use the shared graph candidate service.

The structural index is part of the trusted kernel. Shape fingerprints ignore
snapshots only to select candidates for the existing structural judgment; a
hash match or collision never proves pointer equality, range containment,
initialization, or permission. Each selected occurrence still passes the
original range check. Proved graph aliases do not become structural matches.
Multi-size regressions cover cold hits and misses beside unrelated pointer
parameters, and controls cover partial ranges, consumption, and branch isolation.

This retires the two structural block scans. General read/write permission
also uses the shared candidate service described below, with bounded refusal
outside its supported fragments. Checked resource construction owns attachment: an empty input captures the closed graph
before insertion, and composition advances a prepared lineage. Normalization
already visits its full input and publishes even when no representation changes. These boundaries also
cover temporary contexts built during resource-clause evaluation, independent
of the surface execution-step wrapper. The temporary context for checked
composite/loan projection evidence also uses checked construction. It starts
with only the selected composite head; removing that head and adding dependent
children retains the graph attachment, so a prior child's whole-cell payload
can be selected through transitive address equality. This is part of the
trusted kernel and changes candidate selection only: checked expansion and the
loan ledger still establish the exact parent, children, and authority. Logical
contract loads can bypass permission lookup, so regressions inspect the actual
projection input's attachment in addition to checking expansion and loan
controls. The owned one-level frontier used to adapt a composite view to loan
backing uses the same checked construction. Its temporary context contains only
the selected owned head, and dependent child deltas retain the attachment. This
does not authorize a lend: the adapter still checks the caller's owned coverage,
definition facts, and recovery recipe. The coverage context reconstructed from
that owner's checked children also uses checked construction before consuming
the requested frontier. It retains graph candidate selection while ordinary
resource consumption checks quantity, ownership, and sufficient coverage;
partial consumption leaves only the residual authority in a proof-local fork.
Branch isolation, read width, double consumption, partial coverage, snapshot
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
view refusal, insufficient coverage, preserved snapshots, and multi-size
scaling beside unrelated resources and equalities. The retained supplier
interface below also covers explicit fragment composition; unsupported
symbolic matching refuses without an ambient retry.

An unchecked context with no attachment remains unprepared. Extending a valid
ambient context through a delta-only API does not silently publish all its
unrelated resources; use a whole-input normalization/publication boundary when
attachment is required. Unsupported symbolic containment and retained
load-origin forms refuse when the indexed service cannot select a supplier. Forks of a published
input retain their pairing. An attempted replacement by address anchors alone rejected existing
completed-read and borrowed-buffer proofs whose temporary contexts had no
complete attachment, even when the graph knew their base equality; it is not
part of the implementation. Stored-value
and initialization-evidence spelling lookups remain separate migrations.

Read, write, and fold consumers are integration examples. A lookup must not
enumerate every spelling in a class. Equality indexing narrows candidates;
permission quantities, range containment, ownership reservation, and ordering
still require their own checked judgments and complete candidate indexes.

## Bounded symbolic containment support

Symbolic endpoints cannot in general be sorted into an interval tree. The shared
resource/graph pairing therefore maintains an additional persistent index
for exact symbolic byte footprints beside the existing exact start-address index.
A footprint is a typed
graph application of its start and end address classes. Congruence propagates
late base, scalar endpoint, and retained same-snapshot load equalities through
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
a resource/loan certificate that already selected a supplier can retain its
opaque occurrence handle. Expansion emits ordinary proof source, and fresh
verification reconstructs its checked occurrences and graph registrations.
Borrowed byte and halfword buffers, including nonzero symbolic starts, have an
expansion/rechecking regression. Kernel regressions cover symbolic index bounds,
late endpoint equality, snapshots, sibling contexts, retired occurrences,
read/write authority, and same-base non-supplier scaling at multiple sizes.

The symbolic-byte-extent consumer uses this service exclusively. Unknown or
ambiguous selection refuses without its former exact-base retry or whole-input
scan; the unused `memory_base_facts` consumer API is removed. After selecting
one supplier, the checker inverts explicitly scaled byte counts into that
supplier's element width before ordinary coverage arithmetic. It checks the
selected read core, including quantity; equality does not supply authority.
Consumer regressions cover byte, halfword, and wider footprints, bounded
subranges, missing bounds and aliases, sibling isolation, view and owner
suppliers, and zero quantity. A red-to-green regression rejects an ambiguous
start bucket even when a hidden search could find a covering supplier;
checker and persistent-index work remain flat across 16–1,024 same-base ranges.
Storage and object consumers now use the indexed evidence described below.

General read/write permission uses one shared classifier. Exact address/start
payloads include eligible partial reads; physical interval hits select retained
suppliers even when the index cannot establish complete coverage. A miss is
final only for a complete concrete interval fragment. Otherwise, prepared base
and affine-class summaries can select a sole supplier by cardinality. Symbolic
read starts have their own class payload, so a partition rooted in an outer
storage block does not hide its logical pointer base. A multi-size regression
selects the left partition beside unrelated same-base ranges without searching
them; missing bounds and view-only write authority still refuse. Ambiguous
or unsupported queries refuse before checking. No consumer retries spellings,
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
spelling selected from an ambient graph. Direct support returns the original
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
no resource or loan authority. Candidate delivery is lazy: a direct proof stops
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
It does not normalize unrelated holdings or retry an ambient matching route. Loan-bound and projected
observations keep their original dependencies and cannot be coalesced this way.
Persistent edits install residuals in the consuming fork; siblings retain their
input. The superseded symbolic base-anchor payload, structural start/end
indexes, and `equal_address_entries` helper are deleted. Empty range identity
asks the shared graph whether its endpoints are equal.

A transitive-alias regression was red because direct support searched the
original pointer's shape bucket. It now returns the actual retained owner and
occurrence through the shared candidate interface. Multi-size regressions
measure satisfaction, support, and two-fragment consumption beside 16, 64,
256, and 1,024 unrelated same-base spans. Controls cover holes, insufficient
coverage, residuals, missing aliases, view-only authority, zero quantity,
sibling snapshots, and the existing projection/separation checks. Another
red-to-green scaling regression checks direct support beside 16–1,024
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
from the consuming resource fork. Address equality between different external
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
checked concrete formation as well as its existing original formation evidence;
mutex initialization no longer retries alignment on another pointer spelling.
Explicit power-of-two alignment premises also supply one retained witness on
an address class. Late equality merges keep the strongest original premise;
lookup checks that premise directly instead of enumerating class members.
This supports symbolic aliases as well as concrete storage coordinates.
The formation rule retains any explicit alignment premise and still checks
byte displacement, intrinsic alignment, and requested alignment. The existing
single-premise arithmetic alignment certificate continues to encode only
formation arithmetic; its evidence producer refuses a class witness whose
supporting equalities that certificate cannot express. Ambient alignment
checking does not label such incomplete evidence as a complete certificate.

The old `storage_pointer_spellings`, one-hop
`resolve_symbolic_pointer_alias`, premise-scanning `resolve_minted_load_pointer`,
structural owned-byte span caches, and `memory_block_facts` supplier API are
deleted. `memory_base_facts` was deleted in milestone 5. Remaining block-index
visits apply effects or check all affected occurrences, rather than search
for an implicit memory supplier. Explicit composition/publication and fragment
inputs may be visited proportionally to their admitted input or produced delta.

Regressions cover transitive ownership aliases, view-only and zero-quantity
refusals, typed object identity versus raw address equality, empty footprints,
consumed occurrences and persistent siblings, concrete storage anchors and
ambiguous classes, and several external addresses mapped to distinct storage.
Multi-size checks cover unrelated same-block footprints and composition
sources, hits and misses, and growing alias histories. Existing initialization,
retirement, composition-admission, and contract-projection scaling controls
remain in force. The complete fixture gate verifies expansion and rechecking.

## Resource producer publication audit

Milestone 1 of the repository's egraph issue is producer publication, not
containment completeness. Fresh selected-resource assembly now starts with
`ResourceContext::new_with_equalities(assumptions)`. This kernel service captures
the current closed graph while the resource input is empty. It costs constant
work with respect to ambient resources and equality history; subsequent facts
maintain the paired index through existing resource deltas. It does not check
validity, create authority, or normalize representations. Selected facts still
pass their existing resource, loan, expansion, or certificate checks. The graph
and these indexes are part of the trusted kernel.

The constructor is available inside the crate because surface proof assembly
also creates temporary inputs to kernel resource queries. It does not expose
graph mutation outside the kernel. `unchecked_with_fact(s)` retains an existing
attachment but never publishes an unrelated ambient frame. Use checked
composition when the facts' validity needs checking; its empty-input path
already captures the graph. Whole-input normalization is another existing
publication boundary, including a normalization that changes no representation.

The production audit covers these producer families:

| Producer family | Publication rule |
|---|---|
| Function-call single-view satisfaction, conditional-control frontiers, returned composite/population bodies, and access-mode refinement | Fresh assembly captures its actual assumptions before adding selected facts. |
| Framing and owned-footprint derivation, matched-instance body evaluation, and selected instance load values | Fresh selected heads/ranges start published; expansion deltas preserve attachment. |
| Contract transfer, returned-clause evaluation, allocation support, and definitional resource consumption | Fresh requirement/supply/frontier contexts capture the assumptions used by their consumers. |
| Stable-view planning and loan entailment | Fresh callee and single-supplier contexts start published. Binding checks that intentionally exclude ambient facts use one empty proof context for both construction and entailment. |
| Kernel execution certificates and population authority exchanges | Checked temporary child, authority, and support contexts start published under the certificate's local facts. Path preparation publishes explicitly substituted exit resources once before individual claims query the output. |
| Loop body reset and borrowed contract input installation | Fresh live contexts capture the current assumptions; selected-view/instance deltas retain their parent's publication. |
| Surface dynamic view dependencies, checked returned-resource receipts, and compact composition propositions | Fresh contexts capture the same assumptions used to check their occurrences or receipts. Existing occurrence and loan provenance is preserved. |

Existing checked constructors in composite projection, owned-frontier expansion,
frontier coverage, mutex transfer, and object-comparison support remain unchanged.
Explicit supplier composition in resource consumption starts with the
selected checked input and publishes its normalized result before consumption.
It does not select through a structural or ambient normalization retry.

The retained raw constructors are intentional and have different lifetimes:

| Retained raw input | Why no graph attachment is required there |
|---|---|
| Empty join-abstraction shapes and checked-return certificate placeholders | Used for structural comparison or replaced by checked clause contexts; no unchecked memory is inserted for a live query. |
| The empty residual in reconstructed `CallKeptOwnership` and the empty transfer used when composing loan evidence | They remain empty; actual authority is carried by the recorded ranges or checked loan evidence. |
| Startup static-resource construction | Builds provisional program data before proof assumptions exist. Its live execution input is published at the explicit proof boundary, not by permission lookup. |
| Bitvector/pointer substitution of theorem/state resource terms | Rebuilds structural proof payloads without current assumptions. Old graph equalities cannot be inherited after variable substitution. A live instantiated input is published when admitted to execution. |
| Surface composite-body instantiation and branch-interface collection | Provisional lowering output is explicitly checked/composed before becoming live authority; no permission query attaches it implicitly. |
| Instance field scope and default empty `CState` fields | Lexical instance interpretation or empty data, rather than a memory-authority context. Live resource assembly uses the rules above. |

A new producer must choose one of these publication boundaries and document any
raw lifetime. Do not repair a missing attachment by scanning a cold frame from
a query, and do not call whole-input publication repeatedly for deltas extending
an ambient frame. Published persistent forks retain their index; only admitted
class and occurrence changes are propagated.

The framing regression inspects the actual opened context returned by
`call_kept_ownership`, rather than relying on a successful general permission
check. Before migration it failed to find the exact graph payload through
`a = b = c`. Controls cover sibling isolation and retained source authority.
Additional tests cover late equalities, insertion/consumption deltas, preserved
parent snapshots, and fresh plus framing construction beside 16, 64, 256, and
1,024 unrelated resources and equality facts. Both deterministic query work and
persistent-map work are measured, so deferred publication or a hidden ambient
scan cannot pass merely because the final lookup is cheap.

Publication has an explicit producer policy. Publication alone does not
complete candidate selection: the consumer migrations above establish bounded
selection and refusal. Adjacent storage/object queries use the completed interfaces below.

## Checked pointer-read sources

Typed pointer-read producers now share `PureFactContext::register_pointer_read`.
It records the existing value's load definition and, when the exact defining
snapshot (or its recorded canonical projection source) is a `CellsSeeded`
edge supplying the entire read footprint, admits equality with that run's
source read into the branch's graph. Only load-valued, contiguous, live slots
of the required width qualify. The check inspects the selected slots rather
than the run's extent, address aliases, or snapshot history. Canonical
projection bridges use exact producer registry entries. These are trusted
kernel rules; they introduce neither proposition premises nor access rights.

Ordinary pointer equality queries and resource consumers use the resulting
closure. A later address equality propagates through the registered source
applications without repeating this check. There is no special comparison
rule in `fold`. Producer publication occurs only after a typed read's existing
prerequisites have been checked. The graph's generation invalidates equality
misses recorded before publication; persistent sibling contexts retain their
own admitted unions.

The same producer boundary now handles one immediate `Store` edge. It uses
structural object separation or an exact constant byte gap, after re-expressing
the selected read in the store's block through established graph equality.
It checks the store's full value width against the read footprint and admits
`load(after, address) == load(before, address)` only when their bytes are
separate. The exact byte geometry is shared with the memory checker. It does
not use address inequality alone, scan ownership frames, or walk older memory.
Already admitted single-store edges compose through ordinary graph closure;
unknown store-address aliases require a later producer check once the needed
separation is available. Unregistered intermediate edges remain unknown.

Snapshot producers also maintain an immutable **read identity** for graph
load congruence. A recorded `CellsForgotten` edge inherits its base's identity:
removing cached knowledge changes no program bytes. A load-valued `CellsSeeded`
run inherits it only when the run's source and base already share that identity
and each slot's stride equals its value width. Copying the same bytes already
in the base is materialization, including successive sibling runs copied from
an equivalent earlier snapshot. Other transitions receive a distinct identity.
The pointer and int32 graph-load signatures use this key while the existing
load terms and C pointer values retain their original snapshot representation.

This metadata is part of the trusted kernel and establishes value equality
only. It does not establish snapshot equality, read permission, initialization,
allocation continuity, or framing. Unrecorded pruning, constant or symbolic
storage runs, changed sources, stores, and havoc cannot inherit a key by this
rule. Checked separate-store unions still belong to their proof branch.

The key is fixed at first interning. If a snapshot was already interned without
this annotation, recording a later edge conservatively loses the new equality;
existing graph applications never require relabeling or rescanning. Arena reset
keeps prior-session keys distinct. Production uses immediate-source key lookups
and does not enumerate slots or registered reads. Endpoint queries compose
arbitrarily many already-produced materialization/forgetting transitions with
ordinary congruence, without intermediate read publication or a history walk.
Deterministic regressions check approximately linear production over increasing
histories and constant endpoint-query work. The redundant per-read forgetting
admission rule has been removed.

The recursive unfold → sibling-field write → refold fixture now verifies,
expands, and independently rechecks. Overwriting the pointer field instead
rejects the expanded proof.

A load's equal-cell scan also reads this graph when the cached cells are a
seeded run. A run names the slot a load is at from the byte shift between the
load and the run's base, and a load spelled in another block used to reach the
base only through a stated alias filed under its exact pointer: `id` reached
`p`, while `id + 8` reached nothing and became a fresh load after any store.
`run_slots_equal_to_load` now re-expresses such a load in the run's block
with `pointer_in_block`, one keyed query over the affine class relation, so a
run answers for `id + 8` exactly as a single cached cell does through
`pointers_known_equal`. It selects a cached slot only; it adds no separation,
framing, or read authority: the slot is the one a load spelled at the run's
own address reads from the same snapshot. `mdtests/fold_at_arm_identity_after_store_to_other_node.md`
and its three negatives retain the case.

A retained cell-map entry alone is insufficient preservation evidence:
low-level snapshot construction can leave it present after a write through a
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
Avoid whole-state clones, deep structural cache keys, repeated same-snapshot
load scans, and alias enumeration on each resource access.

Restricted contexts rebuild from the selected premises and required term DAG.
They must not inherit ambient merges or explanations. Fact withdrawal likewise
must invalidate every consequence that depended on the withdrawn fact; either
rebuild the affected context under a documented bound or use a justified
persistent strategy. Execution writes do not withdraw facts about old snapshots.

Deterministic regressions vary multiple input sizes along these axes:

- chains, balanced merges, late merges, and repeated equality queries;
- nested loads and many unrelated loads within one snapshot;
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

Equality substitution now has a kernel-owned checked rule in
`proof/equality_rewrite.rs`. It admits the cited equality through the persistent
exact premise index, computes the substitution, and returns a private checked
result. That result constructs the proposition obligation; surface code supplies
presentation data, not a replacement semantic goal. A different load spelling
must pass the kernel's corresponding-leaf transport check first. The candidate
helper used by smart planning has no proof authority.

The outer quantifier walk refuses binder collisions with the bounded,
carrier-aware variable collector, which treats snapshots as opaque. Direct
regressions cover unavailable/reversed premises, sibling-context isolation,
forged presentation, shadowing, capture, and ambient premise/snapshot scaling.
Source-level exploit reachability was not established. Goal lowering/unfolding
and other transitions through the generic publisher remain separate trust
boundaries; they were not migrated by extracting this equality rule.

Soundness tests include unproved aliases, snapshot changes, incompatible load
interpretations, branch leakage, restricted-premise leakage, offset wrapping,
and tampered equality explanations. Later constructor support must address
injectivity, no-confusion, and cyclic equations under the declared value
semantics. Distinct constants of the same sort produce a contradiction;
constants in different sorts must not be merged at all.

## Migration and deletion

The seven bounded resource lookup cleanup milestones are complete: producer
publication, shared containment and span support, general read/write permission,
symbolic range reads, satisfaction/support/fragment consumption, and adjacent
storage/object queries. Their named spelling retries and ambient supplier
searches are deleted. The completed issue is removed from the open issue list.
The pointer/load foundation is implemented; broader theory and tactic
extensions require a concrete new use case. The historical non-green
loaded-pointer trial is evidence about dependencies, not the implementation
plan. Use isolated worktrees and integrate only coherent
green commits. Preserve the original C regressions.

Delete old mechanisms as their responsibilities migrate:

| Responsibility | Mechanisms to retire |
|---|---|
| Pointer equality and permission lookup | Alias indexes, equality walks, `pointer_spellings`, `resolve_symbolic_pointer_alias` |
| Load identity/equality | Minted-load scans, recursive load normalizer, comparison-time frame search, spelling retries |
| Scalar equality | Lazy bitvector graph, 64-bit adjacency map, `ConstantClasses`, exact constant aliases |
| Algebraic/function congruence | Gap-74 alias retry and duplicated operand-wise equality recursion |
| Tactic matching | Surface bridges made redundant by checked closure queries |

Int32 Boolean consumers now share one graph query. Exact alias enumeration,
premise evidence, constant discovery, and wider scalar theories still retain
their own indexes. For each further consumer migration,
identify the remaining fallback cases, cover them with the intended checked
judgment, and delete the superseded path. Full deletion is an acceptance
criterion, not optional cleanup.

The first substantial handoff is after the pointer/load representation and
closure work through real read/fold consumers, with checked evidence, scaling
regressions, and the full gate passing. That creates bounded consumer migrations
against stable APIs. Bitvectors, algebraic terms, provenance changes, and
certificate changes still require design review when reached.
