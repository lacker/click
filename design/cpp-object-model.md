# C++ object model and shared memory semantics

## Status and purpose

This is the consolidated design target for the bounded C++ object model, with
the shared semantics required by C and Rust. It answers when the current
foundation is stable enough to resume C++ feature work. It does not claim full
C++ semantics or change the implementation by documenting a rule.

The implementation baseline includes the construction work recorded in
[Aggregate construction](aggregate-construction.md) and the explicit output
initialization work in [PR 646](https://github.com/clicklang/click/pull/646).
The [byte representation record](../docs/internals/byte-representation.md)
describes current byte behavior; the [C++ issue](../issues/cpp-support.md)
owns delivery status and source profiles. This document owns the combined
semantic target and stabilization criteria. Where current behavior falls short,
the gap is identified below. Historical delivery notes remain historical.

The principal conclusion is that typed cells, allocation identities, persistent
snapshots, indexed ranges, and the existing resource system remain useful.
We need one set of object and representation laws used by execution and proof,
including modular calls. Replacing memory with a flat byte array would not
resolve lifetime, provenance, or language validity and is not the proposed work.

## Decisions

1. Share the memory machinery and semantic operations across languages. Keep
   language-specific rules for object creation, valid access, moves, borrowing,
   and cleanup explicit at the checked frontend boundary.
2. Distinguish storage, objects, initialized bytes, valid values, and access
   authority. None of these is a substitute for the others.
3. Keep typed cells as the efficient representation. Typed and byte observations
   of the same supported object at the same snapshot must describe one value.
4. Make output initialization an explicit, body-checked effect, separate from
   value postconditions and ownership. Mentioning a read in a proposition must
   not create initialized storage.
5. Preserve destination-directed construction, ordinary value copying, and
   explicit lifetime events as distinct operations. A callee's destination is
   not fresh unless the caller's allocation and contract establish that fact.
6. Stabilize the already selected profile before adding owning containers or
   broader object-lifetime features. The acceptance matrix below defines that
   milestone; verifying one more helper alone does not.

These consolidate the accepted direction. The bounded declared-uint32
observation rule is delivered through the existing checked application syntax.
The admission audit and complete object-model acceptance matrix remain open;
implemented native requirements must retain matching checks at actual calls.

## The bounded target

Use the existing pinned x86-64 Linux LP64 C++20 profile, eight-bit bytes and
little-endian integers. Retain the compiler, header, declaration-identity and
layout checks of each admitted source fixture. Native integer contracts with
checked C++ identities remain the contract boundary, including authenticated
`std::byte`. An unrelated enum with the same representation gets no byte-access
privilege.

The stabilization target covers the existing scalar locals and references,
plain records and supported subobjects, bounded construction/return and trivial
assignment, full-expression temporaries, existing RAII/cleanup cases, and the
selected span/byte-output decoder prerequisites. The first new representation
bridge is a declared automatic uint32 object observed through its four bytes.
It is not a proposal to admit every integer width, heap object, array element,
or record field as a reconstruction destination at once.

Already delivered nontrivial local destruction and bounded exceptional cleanup
remain supported. The narrower restrictions on construction returns do not
retroactively restrict every C++ object to trivial destruction.

Placement construction and storage reuse, unions, general inheritance and
virtual dispatch, broader exceptional construction, arbitrary owning containers,
concurrency, and other targets are outside this stabilization milestone.
Adding them must explicitly extend this design. Their absence does not prevent
a sound, useful bounded model.

## Semantic state

The following are distinct facts the model must represent or derive from checked
evidence. They need not become six new maps or one large mutable object record.
Static importer evidence is sufficient for facts that cannot change within the
admitted profile; dynamic facts belong in snapshots or checked execution state.

| Component | Meaning | Does not establish |
| --- | --- | --- |
| Storage | Allocation identity/generation, extent, alignment, and live storage | An object of an arbitrary requested type |
| Object | Declared/admitted type, layout, containing object and subobject, lifecycle phase | Initialized contents or permission |
| Representation | Typed values and byte fragments describing that storage at a snapshot | Legal access by every source-language type |
| Definite initialization | The selected bytes have been written or otherwise validly initialized | A particular value, or validity for every type |
| Value availability and validity | A language-level value may be used in this phase with this type | Ownership of all reachable storage |
| Authority | Permission to read/write or a checked loan/resource over a range | Freshness, initialization, or object lifetime |

Unknown contents are different from uninitialized contents. Havoc can forget a
value while preserving definite initialization and the declared object type.
This applies to symbolic contract inputs as well as local objects: forgetting
an admitted complete typed cell retains its initialized bytes. Adjacent cells
in a symbolic run remain one interval, without enumerating its elements.
Conversely, obtaining ownership of raw storage does not give it a value.

### Addresses and objects

The existing block-and-offset pointer is the address carrier. A field stays at
an offset in its containing allocation; it does not become a fresh allocation.
Copying a pointer copies its provenance and offset without rebasing it. A copied
self-pointer therefore continues to point into the original object.

An address plus allocation bounds is not a complete typed-access justification.
Access also needs an admitted object/type, alignment, the relevant object or
array domain, lifecycle validity, initialization where required, and authority.
For example, owning a whole record does not by itself authorize scalar pointer
arithmetic across its unrelated fields. A cast changes the access description;
it does not create an object, enlarge a pointer's array domain, or grant access.

For the first profile, retain block/offset and existing layout evidence. Audit
that each admitted operation has the necessary object and access-domain evidence;
add a shared descriptor or certificate field where evidence is missing. Do not
introduce independent object identities throughout memory merely for uniformity.
General replacement in the same storage will require an explicit object-generation
and pointer-designation decision when that feature is selected.

### Pointer designation: a confirmed shared gap

The admission audit reproduced [a soundness defect](../bugs/pointer-arithmetic-crosses-scalar-subobject.md)
in both C and C++: a pointer one past the first scalar member of a record can
read the second member. The shared evaluator checks allocation/range bounds and
finds the second member's cell at the same address. That is insufficient under
either language's pointer rules. This turns the earlier access-domain audit
obligation into mandatory implementation work for the existing profile.

Preserve two semantic identities: the storage address used for aliasing and
cell lookup, and the object/array designation used to justify access. A pointer
value must carry or reference checked designation evidence that survives
copying, storage/reload, casts, calls and snapshot transport. This cannot be
recovered just from the numeric address, current read width, or whichever
ownership range happens to contain the address.

The bounded designation consists of the relevant object/array identity, element
type and extent, position within that domain (including one-past), and the
lifetime evidence needed for access. It may use shared immutable descriptors
rather than expanding every pointer with a complete layout. Scalar members
have a one-element domain; actual arrays retain their array domain. Taking a
member address selects that member's domain without allocating new storage.
Pointer arithmetic preserves the selected domain and checks its bounds.
Dereference separately requires a position designating a live object, not its
one-past endpoint.

Address equality continues to support memory alias reasoning. It does not
transport dereference validity between differently designated pointer values.
The representation must preserve this distinction in equality/hashing and proof
substitution; adding a field to `CPointerValue` while discarding it through
`into_pointer()` or treating it like an ignored qualifier would not suffice.
Pure memory observation at an address and executable typed dereference need
different validity interfaces even when they share the same value observer.

The shared `valid_place(p)` predicate states typed location validity separately
from byte access and initialization. Its source-selected scalar type or complete
record layout, full pointer carrier and memory snapshot remain in the kernel
proposition. A direct entry requirement may authenticate that exact carrier;
actual calls check it through the same record/scalar geometry judgments used by
typed views. The C allocation/access policy and C++ native object policy remain
distinct. Numeric equality rewriting cannot manufacture or substitute a carrier
in a validity fact. Ending a lifetime invalidates the current location without
changing a fact about an earlier snapshot. A disjunctive, conditional or
quantified requirement is not an unconditional entry promise.

Input array extents must come from a checked declaration or explicit contract
validity obligation that the caller discharges for the actual pointer domain.
An ownership clause alone must not silently enlarge an already known member
domain. The implementation audit must identify those obligations at modular
boundaries before claiming general pointer-parameter coverage.

For example, a helper reading `p[1]` may require a two-element input domain.
Its caller cannot satisfy that requirement by combining ownership of two
adjacent scalar fields and passing the first field's address. Actual two-element
array storage can satisfy it. This distinction must survive resource splitting
and rejoining, so the object-domain evidence belongs beside authority rather
than being reconstructed from the resulting contiguous owned range.

For byte representation, an admitted representation-view operation selects the
bytes of one designated object under the selected language profile. It does
not turn every byte of the enclosing allocation into one permissible array.
This must use the same domain mechanism as ordinary typed pointers.

### Checked pointer designation: representation and implementation

This describes the implemented bounded input/member path and the remaining
general pointer enforcement work. It does not claim that every pointer access
is checked against a designation.
Keep `Pointer` as the address term used by cells, aliasing and byte ranges. Put
semantic designation on `CPointerValue`, and retain it in memory lvalues until
the executable access has been checked. Do not put designation in a memory-cell
key: two differently designated pointers can still alias the same bytes.

The value carries a shared immutable domain term. A bounded domain records a
root object witness, an explicit subobject/array selection, its base address,
element description, stride and extent. Position is derived from the pointer's
address relative to that base; do not maintain a second independently mutable
position. A scalar uses a one-element domain. An array element pointer retains
the containing array's domain, while a pointer to one of that element's members
selects that member's domain. Row selection in multidimensional arrays preserves
the selected row's extent, not the flattened allocation's extent.

A root witness comes from a checked declaration or admitted object-creation
operation, or a symbolic interface requirement checked at calls. Allocation
alone supplies storage; its native policy must justify any object established
in that storage. An explicit field/base path
selects a subobject of that root. A requested cast type, an overlapping typed
cell or an ownership range cannot issue a witness. The bounded profile does not
need a new globally fresh identity for every field: root identity plus declared
path suffices while replacement/overlapping lifetimes remain unsupported.
Nominal C++ declaration identity must remain attached to native object evidence;
structural layout compatibility does not establish it.

The carrier distinguishes an explicit domain from an unresolved domain term.
Pointer inputs, pointer-valued loads and modular results can have unresolved
semantic domains; unresolved is not an unrestricted domain. A checked access
must resolve the relevant obligation or refuse. A constant null value has no
object domain. Function pointers keep their separate signature rules. A missing
domain during staged migration must not be advertised as checked pointer
support or used as evidence to repair the padding bug.

Domain descriptions do not contain mutable liveness or initialization booleans.
Those properties belong to the current state and selected language operation.
An old pointer can retain an object identity after its lifetime ends without
making the object live again. Construction, destruction and Rust move/loan
checks therefore remain separate. General same-storage replacement will need a
generation distinction before it is admitted; do not invent transparent
replacement behavior from matching addresses.

#### Producers, transport and consumers

| Operation | Required behavior |
| --- | --- |
| Address of a declaration or declared member | Select its checked object/domain, without allocating new storage or initializing it |
| Array decay or element address | Retain the actual containing array domain; selecting an element does not create a larger array |
| `&*p` in C | Preserve the input pointer's domain under the source cancellation rule; do not create a fresh one-element domain or require a value read |
| Pointer arithmetic | Preserve the domain and check both the originating position and result; permit one-past formation but not access there |
| Typed read/write or reference binding | Check designation, type/alignment and current lifetime, then the separately required initialization and authority |
| Cast | Change the access type/qualifiers under native rules without changing the designated object or widening its domain |
| Pointer copy, field store/load, aggregate copy | Transport the complete pointer value, including unresolved domain identity |
| Address normalization | Rewrite the address spelling without rebasing the domain; a binder substitution maps address and domain terms together |
| Havoc or modular unknown result | Forget the relevant value to a fresh symbolic value/domain pair; do not upgrade it to an unrestricted pointer |
| Provenance-preserving representation copy | Transport the complete pointer value under the existing checked copy operation; raw bits alone cannot supply a domain |

Lvalue formation must retain the carrier until the operation is known. Rejecting
all one-past lvalues immediately would break `&*p` cancellation; dropping the
carrier immediately would permit an invalid store even if reads were checked.
The shared load observer can remain address-based, because observing a snapshot
is not executing a native dereference. Executable reads and writes must cross a
separate checked-access boundary before using that observer.

Pointer subtraction requires the same semantic array domain; equal allocation
identity alone is insufficient. Relational comparisons must use the selected
language rule: ordering within an array and permitted ordering of record members
are distinct cases. A byte representation view keeps the selected object identity
but uses its permitted byte extent and unit stride. Retagging an integer pointer
as a byte pointer must not retain an inappropriate integer stride, and casting
back must not manufacture a typed array. The separate C++ byte-traversal profile
choice below still applies.

The approved bounded pointer/integer profile keeps a 64-bit runtime integer's
numeric bits together with the full immutable pointer from which it originated.
This includes designation, bounds, qualifiers and lifetime dependencies. A
pointer-to-integer cast produces this carrier. Converting back checks that the
bits equal that same origin's address, then restores that pointer with the
requested pointee type. It neither selects another pointer by address equality
nor renews lifetime or grants access permission. A plain integer can convert
to a pointer only when it is proved zero.

Numeric comparisons, integer specifications and `address(p)` expose only the
number. Numeric equality never supplies an origin. Proof rewriting may rewrite
the number while preserving the existing origin; structural binder substitution
must traverse both parts using the existing full-pointer substitution rules.
No new contract keywords are introduced.

Exact full-width stores and loads preserve the carrier. Reading representation
bytes exposes numeric bits; partial writes and reconstruction from bytes discard
origin, even when the numeric result is unchanged. Same-width signedness casts
preserve it. Add, subtract, OR and XOR retain a single origin-bearing operand
(for subtraction, only the left operand); two origins do not select a winner.
AND retains one origin only for a known 64-bit clearing mask whose high bit is
set. Low-bit extraction and unsupported or narrowing operations discard it.
All retained arithmetic still requires the original address to be restored
before cast-back. These are bounded verifier rules, not a claim to model every
implementation-defined native conversion.

Runtime bindings can carry this value directly. A modular postcondition that
states only numeric equality cannot transfer origin to a result or output cell.
Such a boundary requires checked origin transport before it can be admitted;
the initial profile refuses unsupported cases. Implementation and integration
validation of this approved representation are in progress.

Origin retention does not replace lexical lifetime tracking. Native standalone
blocks must retain an explicit `Scope` boundary in the shared statement model.
Its execution reuses the existing scope-exit rules: evaluate a return value
while its locals are live, then retire the scope's automatic objects on each
exit. Source stepping records the same selected lifetime ends, so expanded
proofs cannot extend a local's lifetime by flattening its block. The current C
goto profile already restricts labels to function-body level; admitted jumps
from these inner scopes therefore leave them. This adds no contract syntax or
new ownership policy.

#### Equality and substitution

Distinguish native address comparison from equality of semantic pointer values.
A native `p == q` comparison may hold where the address model permits it even
when `p` and `q` have different domains. That condition can resolve aliasing and
byte-cell lookup; it cannot justify replacing one executable pointer value with
the other. Whole-value equality, stored-value reconciliation, retained proof
keys and substitution must account for designation.

Changing only `CPointerValue`'s Rust `Eq`/`Hash` is insufficient. The current
`c_values_proven_equal_for_memory_resolution`, resource-value matching and typed
rewrite paths sometimes compare or carry only raw addresses. Their callers must
choose deliberately between address equality and full-value equality. Domain
terms must participate in alpha keys, free/bound-variable collection, capture
avoidance and memory canonicalization. Do not use a registry lookup whose
mutable contents silently change the meaning of an already certified value.

A pointer load's symbolic value/domain pair is tied to its exact defining
snapshot and cell. Checked store/load or memory-frame evidence can transport the
whole pair. An unrelated equality about the loaded address cannot select a
sibling domain. This retains the existing indexed read-identity machinery,
but requires an explicit distinction between read-address evidence and evidence
about the complete value stored there.

#### Interfaces and the constructor-padding proof

Each native contract carries separate domain obligations alongside its existing
permission and initialization obligations. Source entry assumes those domain
obligations for symbolic values; the call checker must discharge exactly those
same obligations for actual values. A raw pointer parameter's type alone does
not require a live pointee. A native reference has its language-specific referent
requirements. Typed access requirements in an existing contract can supply a
valid-object/span obligation independently of the resource that supplies access
authority. Bare byte ownership cannot establish a typed object or array.

An array-span requirement means the requested positions belong to the pointer's
actual domain; it does not resize the domain to the owned interval. Splitting or
joining permissions leaves that requirement unchanged. In particular, owning
both `pair.first` and `pair.second` cannot satisfy a two-element array requirement
for a pointer obtained from `&pair.first`.

A modular pointer result or pointer-valued output needs checked designation
postconditions, just as initialization needs checked effects. These can preserve
an input's domain, select a declared child, or describe a legitimately created
object. An address-only postcondition `result == input` is insufficient to
establish domain preservation. Initially, derive only relationships that the
native interface/body checking actually certifies; keep unresolved results
unusable for accesses that need missing evidence. Do not add a hidden promise
that every pointer-returning helper preserves a particular input's domain.

Loop abstraction has the same obligation. A fresh abstract address may retain
the entry pointer's designation only when the loop rule checks preservation of
that complete designation on every relevant body continuation. Numeric loop
invariants can then establish the address's position within that domain; they
cannot supply its identity. Joins likewise retain only common checked
designation evidence. A changing or unsupported designation must remain
unresolved unless a separate checked invariant describes it.

For `Restore`, establish the constructor destination's object and the input's
live scalar object under matching entry/call obligations. In the supported
non-overlapping object hierarchy, a live scalar cannot occupy arbitrary padding
of an unrelated live/constructing object. The input may still designate a real
field of that object; existing ownership obligations must reject forbidden
aliasing in that case. Distinct symbolic names or distinct witness labels alone
never establish separation. Unions, byte-array storage provision, replacement
and other overlapping-object cases require their specific rules before they
can use this argument. The destination's padding stays unwritten throughout.

#### Delivery and validation order

1. Replace metadata-dropping pointer transformations with complete-carrier
   transformations. This preserves today's qualifier behavior and creates a
   reviewable prerequisite; by itself it does not issue or check designation.
2. Add domain terms and semantic equality/substitution support together. Cover
   stored pointer values, loaded symbolic pairs, binder substitution, snapshot
   identity and retained keys before enabling producers. Raw address equality
   must remain available for aliasing.
3. Retain domain information through lvalues and add checked declaration,
   member and array producers plus arithmetic/read/write consumers. Enable a
   coherent bounded path only when its casts, copies, loads and calls cannot
   discard the evidence. Unsupported crossings must refuse, not fall back to
   permissive address-only checks.
4. Check native input-domain requirements at actual calls and symbolic body
   entry. Use authenticated object relationships together with checked
   complete-width ownership separation to repair the unchanged constructor
   input read. Modular pointer-result and pointer-output designation effects
   remain a separate requirement before broader producer activation.
5. Close the sibling-pointer bug only after its direct, local, stored/reloaded,
   cast, modular-call and equality-rewrite variants are rejected in ordinary,
   expanded and retained verification. Preserve valid direct sibling access,
   scalar `+0`, permitted one-past formation/comparison, array traversal and
   supported pointer representation copies. Audit C, C++ and Rust producers.

The carrier, lvalue and load-pair foundations are implemented, with bounded
native input and member selection. The optional shared descriptor distinguishes
legacy absence, an unresolved pointer binder, an immutable loaded-value origin,
and an explicit root/path/base/element/stride/count term. Counts and array path
selections are mathematical integers. Value identity, snapshot identity, alpha
keys, dependency collection, full-value substitution and resource matching retain
these terms; address-only substitution cannot replace them. Raw pointer comparison
and storage keys remain address-based. Resource semantics version 75 invalidates
older retained artifacts.

Native input spans are minimum guarantees, not declarations of the complete
allocation's extent. A scalar prefix records its declared element type and a
mathematical count; a record prefix also records its checked nominal layout.
Selecting a record element or member retains the exact input identity, origin,
and selection path. Authentication checks that row and path and carries the
selected element's bounds into the ordinary proof obligations. It must not find
an input witness by numerical address equality or reinterpret a promised prefix
as a complete array object. An empty prefix gives no object, non-nullness, or
executable access guarantee.

Record-pointer arithmetic retains the source's record layout and unscaled index
as a typed operation. Its stride is the checked record size, with subtraction
applied outside the native index's modular arithmetic. Lowering it to generic
byte-pointer arithmetic would discard the distinction between traversing record
elements and accessing an object's byte representation; those operations have
separate requirements.

This descriptor is syntax, not an authenticated object witness. Declared scalar
address formation and native record/member selection authenticate the declaration
or retained input requirement before issuing an object descriptor. C++ layouts
retain a nominal token from the locked import identity and validated declaration
USR; equal geometry alone cannot substitute a different declaration. A member
retains its enclosing root and explicit path, including an offset-zero child.
Cast or offset arithmetic cannot turn that path into a sibling selection.

The admitted int32 and const-int64 references, native record references and
receivers have matching symbolic-entry and actual-call requirements. The bounded constructor profile also retains
typed scalar validity from an unconditional direct int32/int64 input cell clause.
Requirements are part of the semantic interface and survive annotated contract
reconstruction. They grant neither ownership nor initialization. A missing or
unauthenticated descriptor refuses these calls; an address equation cannot repair
it. Retirement drops input witnesses that may overlap freed storage unless
complete separation is checked. Automatic declaration evidence remains tied to
its own lifetime; these inputs never manufacture a declaration or allocation. Geometry matching is indexed and memoizes fully checked selected-layout
matches; lifetime and current-memory authentication remain separate checks.

**Producer activation remains bounded.** The pinned C++ importer marks admitted
raw object-pointer parameters as native inputs, independently of their resource
clauses. Their symbolic entry values start unresolved even when the contract
has no span requirement. The marker is part of the checked function interface;
it grants no object extent, permission, or initialization. A typed input promise
can justify traversal; the absence of a promise must not select legacy pointer
arithmetic. Existing unprofiled C and Rust parameters and unknown pointer
loads retain legacy absence. C records containing unions remain outside automatic
native record enrollment, including records holding modeled opaque pthread
objects. This compatibility boundary does not admit C++ union operations or
weaken explicit native input requirements. Exact known pointer stores and reloads preserve the
complete carrier. An immutable loaded-value origin can transport a designated
value through its own checked complete cell and memory history, but a registry
name, cell extent or pointer type is not evidence about the referent. The origin
and raw loaded address must be rewritten as a pair. Resolution memoizes shared
copy prefixes within the exact assumption and memory-history scope.

Do not enable designated unknown outputs globally before modular contracts can
certify full pointer-value effects. Existing address-only postconditions do not
promise designation preservation. An unknown summary output therefore cannot
satisfy a new native object-input requirement. Executable arithmetic, subtraction, ordering, reads and writes now check
retained domains. Automatic scalar arrays and scalar/record globals retain
checked declarations; scalar array members decay with their actual extent.
Reference binding preserves an actual array element's containing domain.
Complete loaded carriers require their exact full-width defining read and
checked cell history, independently of raw address equations.

Body-certified result effects preserve an input domain or select a declared
child. They require independently reconstructed contract entry, independent
symbolic binders, and agreement across complete normal-return paths. Independent
parameter names alone are insufficient: caller-specific cell contents or extra
entry assumptions must not certify a universal result, stored-pointer equation,
or native output guarantee. The shared entry recipe must admit exactly the
function's declared storage, native input requirements and contract resources.
It can reconstruct an explicitly declared opaque composite head from the
independent arguments and indexed definition. It does not unfold that head,
import caller cells, or guess selected child, protocol or resource-reference
evidence. The actual entry must still match the reconstructed memory, complete
resource representation and declared premises exactly. The new opaque-head
and native-formal enrollment checks require integrated validation.

The bounded stored-pointer effect certifies an exact final full-width member
cell containing the selected source carrier on every complete body path.
Application checks its declared member type, write permission and initialized
width before retaining that carrier. A numeric pointer postcondition supplies
only address equality; it cannot substitute another designation or certify
this effect. Existing
[`pointer effect tests`](../src/kernel/functions/pointer_result_effect_tests.rs)
pair a complete member-store positive with caller-specific cell and extra
entry-premise refusals. The
[`opaque entry tests`](../src/kernel/functions/independent_entry.rs)
check that the head supplies no hidden cell and reject changed carrier,
premise or definition evidence.

A checked call with no applicable effect leaves
its pointer result unresolved. Unknown pointer-cell reads through designated
storage also retain an unresolved loaded pair. Pointer/integer transport is
being migrated to the full-carrier integer representation described above;
numeric-only recovery remains unsupported.

These checks do not yet complete the general interface migration. Bounded
scalar/record span requirements, pointer-result effects and final pointer-member
equations are implemented. Their source/call integration remains under
validation; general pointer outputs, broader result origins and unsupported
aggregate-array/overlapping layouts remain separate obligations.
Legacy absence must not be presented as authenticated support. The
sibling-pointer bug remains open until its full cross-boundary matrix passes.
The unchanged constructor and scalar-unwind integration tests, all four original
cleanup Markdown fixtures, and `basic-cpp` passed the preceding constructor-input
checkpoint. They remain required acceptance cases for designation activation;
scalar-prefix input and pointer-valued output transport are still under
integration. Retain the original source, contracts and value/frame claims.

Queries must use the selected domain/object and existing indexed evidence.
Separation used to frame a read must cover its complete byte span and the
complete changed span. Unequal starting addresses, or ownership of narrower
cells at those addresses, do not establish that separation. Stores, lifetime
ends and call/loop effects must retain evidence that rechecks those extents.
Range membership must use exact byte displacement, not a wrapping scalar index
with the same residue. When a range proof consumes bounds, its certificate must
retain those selected premises so checking does not depend on ambient facts.
Substitution and checked rewriting must preserve the recorded width of each
typed observation, including quantified loads. Combining observations keeps
the wider extent; an unrecorded load keeps its conservative width. These width
facts describe observations and do not establish object designation or access
authority.
Domain transport cannot scan sibling declarations, unrelated cells, the whole
fact environment or snapshot history. Use shared immutable descriptors and
persistent state facts; measure deterministic work at multiple domain, sibling
and unrelated-state sizes. A large array domain is a compact extent, not one
new object record per element.

### Lifetime is not a single initialized flag

Storage can exist before construction and after an object's lifetime. A scalar
declaration without an initializer can establish an object whose bytes are still
unwritten. A constructor can initialize and access some subobjects before the
whole result is complete. A successful constructor summary certifies completion
of its modeled value fields; it does not initialize padding.

Destruction has a language-defined phase with permitted accesses and cleanup
obligations. Do not model it as simply invalidating every access before running
the destructor body. Normal exit, early return, full-expression cleanup and the
admitted exceptional paths must use the same checked lifecycle protocol.
Unsupported exceptional construction remains refused; failure must not invent
successful completion or roll back effects that already occurred.

Rust adds an important independent distinction: a move can consume the usable
value while the storage and old bits remain. Rust live/drop state must prevent
use of that value. A C++ move constructor generally leaves its source object
alive and destructible. Sharing an operation named "move" cannot erase that
difference. Similarly, C++ references do not acquire Rust's exclusive-borrow
rules simply because both use the shared pointer carrier.

## Shared operation contract

Each frontend must justify these operations with its own checked source rules.
The kernel then applies their shared effects consistently, including at calls.

| Operation | Required evidence | Resulting effect |
| --- | --- | --- |
| Allocate storage | Checked extent/alignment and allocation kind | Fresh live storage and the specified owner; no fabricated contents |
| Select construction destination | Exact pointer, layout, range and authority | Bind that destination before execution; no extra freshness assumption |
| Begin object/subobject use | Admitted declaration or construction rule | Record/validate type and lifecycle phase; no arbitrary reinterpretation |
| Initialize scalar/field | Valid destination, conversion, phase and write permission | Store the converted value and mark the written range initialized |
| Read typed value | Valid object/access type, phase, alignment, initialized representation and read permission | Observe the value at that snapshot |
| Assign/store | Existing writable object and valid converted value | Update affected representation; preserve object identity |
| Copy a value | Valid initialized source and destination operation | Copy modeled values, including pointer provenance; no pointer rebasing |
| Copy representation | A checked representation-copy rule and covered source/destination | Transport supported representation and initialization under that rule |
| Complete construction | The selected destination and required initialized value fields | Certify completion; no allocation, copy or padding initialization |
| Move or consume | Language-specific move and cleanup evidence | Transfer value/authority as specified; change source availability only as justified |
| Destroy/end lifetime | Checked cleanup order and lifecycle event | Apply cleanup, retire the relevant object/storage and resources as appropriate |

Initialization is not assignment with a temporary const override. Shared scalar
initialization performs evaluation and conversion, initializes once, then freezes
the admitted const destination. Assignment must not reuse that privilege.

Value copying and representation copying have different preconditions. Existing
aggregate field-copy returns do not imply byte-for-byte padding preservation.
The recognized `memcpy` contract is a separately reported external assumption
with a checked kernel representation-copy effect. Neither mechanism licenses
arbitrary object creation from four byte cells or pointer creation from bits.

Construction-return mode continues to bind the caller-selected destination
before the body. Ordinary copy returns continue to copy. Trivial assignment
from a constructed RHS uses a distinct temporary followed by assignment and
full-expression retirement. Ending that descriptor temporary does not end the
lifetime of independently owned span backing storage.

## One representation, consistent observations

### The delivered declared-uint32 law

Execution loads and specification observations must agree whenever both refer
to the same admitted object, byte range and memory snapshot. A modular call
changes which facts are known; it must not change what a byte or typed read
means. The bounded declared-uint32 profile now supplies this shared relation,
including the unchanged modular C word-value fixture. Other representation
profiles and the remaining object-model acceptance obligations are separate.

For the initial declared uint32 profile, let `w` be its value at snapshot `M`
and `b0` through `b3` be its initialized representation bytes at that same
snapshot, in increasing address order. The semantic equations are:

```text
bk = (w >> (8 * k)) & 255             for k = 0, 1, 2, 3
w  = zext(b0) | (zext(b1) << 8) | (zext(b2) << 16) | (zext(b3) << 24)
```

These are semantic notation, not proposed proof syntax. Their applicability
requires the selected target, a known declared uint32 object, valid byte access,
the corresponding ranges/snapshot, and sufficient initialization for the
observation being used. Four bytes allocated as a byte array do not establish
a uint32 object. A requested load width, cast, or allocation size cannot supply
the missing type evidence.

A typed store followed by byte observations uses the first equation. Four
initialized byte writes, in any order, followed by a typed load use the second.
A partial byte update to an existing initialized word preserves the remaining
bytes. After modular output initialization, postconditions fixing all four bytes
must determine the same word as inline execution would. Old-snapshot bytes
cannot reconstruct the current word after a write.

The initial implementation exposes one guarded representation observation
operation and checked projection/reconstruction rules to both execution and
logical loads. Separate APIs remain for program reads and pure term construction:
program reads have authority and definedness obligations that building a symbolic
proposition does not discharge. In particular, constructing
a logical read term or naming an unknown value does not initialize memory,
start a lifetime, or make an otherwise invalid program read legal.

### Representation and implementation

Keep typed cells authoritative for supported complete values, with byte fragments
and lazy projections where needed. This is an encoding of the common semantics,
not a second independent memory. A store must update or invalidate overlapping
views; a proof cache must include the memory snapshot and interpretation needed
to prevent stale reuse. Joins keep only facts and definite initialization justified
on both paths. Havoc removes value constraints without reviving earlier contents.

Pointer representation remains opaque in this profile. Complete representation
copy can preserve pointer provenance under its existing checked rule; byte
editing cannot manufacture it. Float, Boolean, padding and other unsupported
representations remain outside the new projection/reconstruction rule. A model
can preserve padding without exposing a determinate padding value to a proof.

No eager expansion of every object into bytes is required. Lookup starts from
the selected object/range, uses indexed overlap and declaration evidence, and
does bounded work per supported scalar width. Symbolic ranges use the existing
indexed interval machinery. Unrelated heap cells, resources and propositions
must not be scanned. Proof checking must remain proportional to the selected
input and relevant delta, up to indexing factors. A representation certificate
records the selected evidence rather than asking retained checking to rediscover
an unbounded set of equalities.

An explicit reconstruction lemma can expose the shared law to users when useful.
It must be derived from that law, not become an alternative per-helper memory
model or a mandatory workaround for ordinary typed/byte consistency.

### Implementation boundary for the uint32 bridge

The shared observation interface must take the selected snapshot, address,
observation kind and checked declared-object evidence. The observation kind
includes width: a uint8 read and a uint32 read at the same address are not
interchangeable terms. Execution additionally checks access designation,
authority and definedness; logical term construction cannot discharge them.

For a supported declared uint32 object, choose one canonical symbolic word for
each relevant snapshot/object observation. Its four byte observations are
projections of that word. A checked packing rule relates four known byte
observations at that snapshot to the word, including after a modular call.
Neither projection nor packing allocates storage or sets initialization bits.
The explicit initialized-range effect supplies that independent evidence.

The shared load/representation layer uses `canonical_form_of_load` with an
explicit four-byte observation width. Immutable automatic declaration metadata
pins the checked uint32 type and little-endian target profile. The selected live
load retains its initialization snapshot even when its load variable names
an earlier memory projection. The checked `declared_uint32_from_bytes` application
connects its four byte observations to a constant word; source expansion retains
the exact byte premises at a recorded snapshot where the local remains in scope.
Ordinary, expanded and retained checks, missing/mutated premises and result,
wrong root/snapshot, incomplete initialization, unsupported profile, and
unrelated-fact/cell scaling have focused regressions. No mutable cell observation,
cast, or arbitrary allocation issues the declaration profile.

This is the implementation contract, not a requirement to replace every existing
load term immediately. Existing complete typed cells and direct byte-store
normalization can remain efficient encodings if both reduce to the same law.
The shared C fixture now proves the exact word value without changing its
program or contracts; its character-pointer rules supply the source traversal.
C++ coverage still depends on its separately admitted traversal profile and
unchanged integration proofs. This result does not complete the wider
object-model or decoder acceptance matrix.

## Contracts, proof entry and modular calls

Keep four kinds of information separate: value propositions, initialized-range
effects, authority, and object/lifecycle evidence. For example, the delivered
`ensures initialized(p[0..N]);` atom supplies definite initialization, an ownership
clause supplies access, and byte equalities supply values. None silently supplies
the others. It also does not create a different object type in the range.

The current atom is deliberately bounded: a top-level normal postcondition on
a mutable native byte-pointer parameter or a selected byte-pointer field of a
supported by-value record, with zero start and constant byte count. The address
is frozen at entry. Parameter or descriptor reassignment cannot redirect the
guarantee. Selecting a descriptor field checks its retained layout and complete
initialized pointer value; it does not grant backing storage or object validity.
Body verification starts that output footprint unwritten; holes,
no-op bodies and premature reads are rejected. Calls transfer precisely the
checked initialization effect. Conditional, exceptional, callback and ordinary
external initialization guarantees remain outside this profile.

Explicit external construction-return contracts are a distinct existing
assumption mechanism. They may assume completed initialized value fields for
the designated result, and are reported as external assumptions. That exception
must not accidentally authorize external initialized-range effects on arbitrary
output buffers.

A permitted mutable footprint is an upper bound on byte writes. Checked concrete
body evidence can establish a smaller footprint without changing ownership or
lifetime transfers. The delivered refinement covers a primitive return, alone
or in a scope with no declarations: expression evaluation changes no memory.
Construction, aggregate results, program entry, and external body placeholders
do not qualify for this refinement.

Proof-entry naming must be observational. It can give a name to a value allowed
by the contract, but cannot execute a store into raw output or turn a constructor
placeholder into a completion certificate. Body checking must consider every
aliasing arrangement admitted by the entry contract. Constructing a convenient
fresh proof slot is not a substitute for proving separation.

Copy materialization, initialization queries and snapshot transport must receive
the actual checked call context. Discarding its separation facts can make valid
input cells appear to overlap unwritten output; assuming separation without the
facts would be unsound. Both problems belong at the shared operation boundary.

That context includes separation justified by the ownership partition, as well
as explicit separation propositions. A raw destination must not make every
possibly aliasing symbolic input unreadable after the contract has established
the relevant separation. Conversely, different pointer names are never enough.
Constructor value-field footprints and padding must be distinguished: requiring
authority over value fields must not silently become a requirement to own or
initialize all padding. Resolve these questions by checked range and object
evidence, not by freshening the destination or seeding it with input values.

Execution, modular summaries, expansion and retained checking must apply the
same laws. A checked summary carries the operation's destination/effect metadata
and binds it to actual arguments; it cannot replace the caller's object type or
provenance with a convenient callee interpretation. Semantic changes require
the existing proof/artifact identity invalidation discipline.

## What stays language-specific

| Question | C | C++ | Rust |
| --- | --- | --- | --- |
| Why does an object/value of this type exist? | Admitted declaration or supported allocation/effective-type rule | Checked declaration, layout and construction/lifetime rule | Compiler-derived storage, initialization and move/drop protocol |
| Why is this alias/access legal? | Selected C type and character-access rules | Selected C++ type, object/subobject and authenticated byte-access rules | Admitted reference/borrow/raw-access rules and compiler evidence |
| What does copying or moving mean? | Admitted scalar/aggregate copy | Resolved copy/move/assignment operation and allowed elision/temporary behavior | Copy versus consuming move and associated availability/drop state |
| When does access cease? | Selected C lifetime and pointer-validity policy | Object/storage lifetime plus construction/destruction access rules | Storage lifetime, value availability and loan validity |

This table is an obligation on admitted operations, not a claim that every
language rule listed has a general implementation. In particular, the existing
C11 dead-pointer policy must not silently become the rule for every C++ pointer
comparison or Rust value. C's character-alias rules must not grant C++ access
through every same-sized scalar type. Unsafe Rust is not implicitly covered by
safe-Rust import evidence.

### Bounded C allocated scalar access

The approved compatibility rule keeps C allocated access separate from native
object validity. A successful trusted allocator operation may retain an exact
scalar-access identity for its result. An allocation contract, an equal numeric
address, a cast, or initialized bytes cannot manufacture that identity. Source
lowering must distinguish a real scalar allocation target from the scalar
pointer encoding used internally for record addresses.

The initial profile supports the selected scalar type at aligned positions
within the retained allocation extent. It does not claim general C effective-type
or aliasing support. Allocation grants no initialized value: malloc bytes remain
uninitialized, while calloc follows the separately checked zero-initialization
rules. Every access still needs permission and every read needs an initialized,
compatible value. Free, failed allocation and replacement allocation must retire
or transport the exact identity consistently with storage lifetime.

Typed-place requirements carry their access policy. A C requirement can accept
either native object evidence or this bounded C allocation evidence. A C++
native-object requirement accepts only native object evidence. Symbolic C entry
may assume its declared typed-place guarantee without inventing a concrete
allocation, and actual calls must discharge that guarantee. These distinctions
belong to interface identity and certificate reuse, not to a numeric-pointer
fallback. Implementation and acceptance tests for this rule remain in progress.

Address equality in branch and callback contracts remains an address fact.
Contracts whose implementation dereferences a loaded or returned pointer must
guarantee a valid typed place for that actual pointer. Preserve the original C
and keep insufficient address-only contracts as rejection tests.

The C++ importer must retain enough evidence to distinguish source operations:
resolved constructor/copy/assignment identity, destination category, object and
field layout, qualifiers, reference versus value result, and cleanup sequence.
Clang accepting a translation unit is necessary extraction evidence, not proof
that arbitrary runtime accesses in it have defined behavior.

Preserve the construction design's copy-equivalence restriction. C++20 can permit
additional temporaries for some trivial class results; selecting a result object
in the kernel does not prove that all source executions preserve its physical
address. An identity-sensitive self-pointer example tests the kernel destination
mechanism, but is not by itself a sound source-level trivial-return theorem.
Optional NRVO and broader identity-sensitive returns stay outside that admission.

The audit must also identify the exact C++20 rule or adopted defect resolution
justifying byte traversal over the selected object's representation. Do not
silently use a later standard's wording or an LLVM byte-address calculation as
the source-language justification. If the pinned profile needs an explicit
extension or cannot justify an admitted pattern, report that boundary before
expanding it. This is a source-semantics audit obligation, not a claim that the
existing fixture has a reproduced defect.

### Byte access requires an explicit source-profile choice

The audit compared the imported `c++20` profile with
[N4861 expressions](https://github.com/cplusplus/draft/blob/n4861/source/expressions.tex)
and [N4861 basic types](https://github.com/cplusplus/draft/blob/n4861/source/basic.tex).
The aliasing exemption in [basic.lval] allows `char`, `unsigned char` and
`std::byte` access, but does not by itself supply an array of representation
bytes to the pointer-arithmetic rules in [expr.add]. The trivially-copyable
byte-copy guarantees in [basic.types] are a separate rule and do not justify
every in-place cast-and-index sequence.

The authors' [P1839R5 rationale](https://github.com/timuraudio/p1839/blob/main/P1839R5.md)
explicitly identifies the object-representation pointer problem and limits that
revision to reading; it excludes writing because of additional difficulties.
The [committee tracking issue](https://github.com/cplusplus/papers/issues/592)
records later revisions, including R7. That history is not evidence that the
current pinned C++20 profile already includes a suitable read/write rule. Do
not silently import a proposal or call it an adopted defect resolution without
checking its exact wording and status.

The pinned compiler profile includes an additional bounded implementation
contract. This traversal is not claimed as a literal C++20 guarantee.
Its versioned marker is
`clang19_1_7_lp64_le_declared_uint32_bytes_v1`. It applies to Clang 19.1.7 on
`x86_64-unknown-linux-gnu`, with LP64 pointers and `unsigned long`, eight-bit
bytes, and a four-byte `unsigned int`/uint32 object on the little-endian target.
The exporter records the actual widths and byte order; import validation checks
them and the configured supported marker. The approved marker is the default
of this bounded import profile, and an explicitly different marker is refused.

The contract permits reading and writing a live declared uint32 object's four
representation bytes through the admitted byte view. An authenticated native
uint32 prefix with exactly one element supplies that same selected live word;
it does not identify the enclosing array's end or admit a multiword byte array.
This includes checked byte pointer formation within that extent and its one-past endpoint. Dereferencing
the endpoint remains invalid. Each byte at offset `i` denotes bits `8*i` through
`8*i+7` of the same selected uint32 snapshot. Four initialized byte values
therefore determine the word under the shared packing law. Partial writes do
not complete initialization, and stale snapshots do not determine a current
value. Every operation still requires its independent permission,
initialization and lifetime checks, and retains the original object and pointer
domain. The assumption creates neither an array object nor a different scalar
object; casts and byte ownership cannot supply those facts.

This guarantee does not cover arbitrary records, other scalar representations,
or same-sized substitute enums. Genuine byte arrays keep their ordinary array
rules. The pinned `std::byte` declaration must still be authenticated, and the
standard-library catalog's explicitly assumed contracts, including
`std::as_writable_bytes`, remain a separate boundary. No general language-law
claim is made for the compiler extension.

The selected standard-library bridge additionally assumes source-to-model
equivalence for the pinned `std::span<unsigned int>` constructor,
`std::as_writable_bytes`, and `std::span<std::byte>::data`. Their model bodies
use ordinary checked stores, loads and casts; those bodies require independent
certification before supplying modular effects. Selection checks the exact
function identity, receiver/signature, nominal record layout, declaration header
and locked span-header digest. A missing or different pin supplies no model
effects. The word constructor and writable-byte conversion require exactly one
word; these contracts do not claim general span conversion coverage. The
library equivalence assumptions are separate from the compiler byte-access
assumption and from proofs of the model bodies.

Artifact schema 60 requires the marker and target facts in both the semantic
artifact and import lock. They participate in import identity; older artifacts,
missing or changed markers, and mismatched target dimensions cannot silently
authenticate a proof under the new assumption. Import locking, verification and expansion audit report the marker
through the existing explicit runtime-assumption format. Compiler execution
probes may corroborate this contract, but are not proofs of a general C++
standard guarantee. This resolves the source-profile decision; implementation
and the unchanged decoder's complete acceptance obligations must still pass.

## Implementation assessment

| Area | Current evidence | Remaining obligation |
| --- | --- | --- |
| Allocation, ownership and snapshots | Shared block/offset storage, persistent memory, exact local byte ownership | Reuse; audit object/access-domain evidence at admitted operations |
| Construction and copy | Destination allocation/binding/completion, field-copy returns, constructor summaries and temporary retirement | Check that every path obeys the combined lifecycle laws; preserve language restrictions |
| Initialization | Raw output state, indexed initialized runs, joins, explicit normal output effects | Apply consistently at all entry/copy/summary boundaries; no naming stores |
| Integer byte view | Execution projection/update and declared automatic uint32 assembly | Common guarded observation semantics for execution and specifications |
| Pointer representation | Provenance-preserving complete-cell copy; byte forging refused | Preserve refusals and provenance under common observation machinery |
| Language validity | C++ identity/layout/lifetime checks; Rust move/drop and borrowing checks | Make the evidence boundary explicit; do not infer legality from ownership alone |
| Modular byte-output value | Initialization and individual byte results check | Prove the exact typed word from those same byte facts |

Implementation starting points are `CBlock`/`CMemory` in
[`src/kernel/primitives.rs`](../src/kernel/primitives.rs), initialization and
proof-entry naming in
[`memory_state.rs`](../src/kernel/primitives/memory_state.rs), byte observation
in [`byte_view.rs`](../src/kernel/eval/byte_view.rs), and destination completion
in [`construction_return.rs`](../src/kernel/functions/construction_return.rs).
The C++ scalar and lifetime modules and Rust move lowering retain the language
evidence; moving all their policies into an undifferentiated kernel flag would
be a regression.

The recent failures exposed boundary inconsistencies rather than evidence that
typed cells must be replaced: proof-entry naming could initialize raw output;
copy checking lost useful separation context; execution byte reads and logical
byte reads had different available relations. The output-initialization work
repairs the first two boundaries. Its returned-observer regression is repaired
by naming logical inputs with checked explicit separation facts. The constructor
repair combines authenticated nominal-record and scalar input requirements
with complete-width separation from distinct owned members of a valid
composition, including members in different pointer blocks. The unchanged
constructor and scalar-unwind integration tests, four cleanup Markdown fixtures
and `basic-cpp` pass.
Neither repair changes source contracts or initializes padding. The bounded shared C byte/word bridge is now checked normally, in expanded
source and in retained sessions. Broader pointer designation enforcement and the
remaining frontend/object-model acceptance matrix require their own validation.

### Audit ledger

The following records the focused audit, not a certification of all C++ behavior.
Source admission, execution and proof checking each have separate obligations.

| Path reviewed | Evidence inspected | Result / required action |
| --- | --- | --- |
| Standard byte identity | `cpp/scalar.rs`, `cpp/validity.rs`, exporter cast checks and pinned-declaration tests | Nominal identity and scalar backing are checked; this does not establish traversal semantics |
| Member address and arithmetic | `cpp/lowering.rs`, `CPointerValue`, `eval/operators.rs` and `eval/memory_loads.rs`; original C/C++ probes | Native declaration/member producers retain authenticated root/path selection; general arithmetic/access enforcement and the sibling-pointer defect remain open |
| Construction return | `cpp/construction.rs` and the implemented construction design | Preserve value-only/copy-equivalent admission; kernel destination identity alone is insufficient for source return identity |
| Entry initialization | Raw markers, naming, checked entry facts and the constructor regression | Keep raw output and padding unwritten; the constructor repair requires authenticated object witnesses and complete field separation, including indexed cross-block ownership composition |
| Returned observer | Recorded proof trace and unchanged integration test | Input naming now uses already checked explicit full-range separation; ordinary, expanded, retained and negative checks pass; constructor padding uses the separate bounded object-input rule |
| Byte/word values | Shared uint32 observation/packing, pinned automatic declaration metadata and the unchanged exact modular word fixture | Ordinary, expanded and retained checks and certificate mutations pass for the bounded shared C profile; other representations/frontend coverage remain separate |
| Rust availability | `rust/lowering/moves.rs` storage events and checked live/drop flags | Preserve value consumption independently of bytes and storage; a C++ move must not reuse Rust's consuming semantics |
| Scalar initialization | Shared initialized declaration, conversion and const-freezing protocol | Retain the distinct initialization transition; ownership and a named logical cell cannot replace it |

The bounded constructor-padding rule retains the complete raw marker and never
initializes or discards its padding. Matching entry/call requirements establish
the destination's nominal record and the input's live scalar object. In the
admitted non-overlapping hierarchy, a scalar cannot occupy arbitrary record
padding; complete separation from every value field therefore excludes the raw
destination. Indexed ownership composition supplies that field separation
across the receiver and input blocks. A field-owner partition without those
object witnesses is insufficient, as are distinct pointer names, address
inequality, or separation covering only part of a field. Unions, replacement
lifetimes and other overlapping-object profiles remain outside this rule.

### Constructor-padding implementation sequence

The `Restore` regression cannot be repaired just by passing more ownership
facts to the raw-footprint query. Its input integer is separate from the two
owned fields, but that partition says nothing about the four padding bytes.
The constructor binder checks destination selection, alignment, live storage
containment and field permissions. It requires a nominal declared complete layout
or explicit child boundary, or the matching input requirement of an enclosing
symbolic proof. Scalar inputs and native record references now carry separate
object-validity requirements with the same actual-call checks. Contract
certification uses these same binders; it cannot invent an input object.

Complete automatic aggregate declarations now retain their layout in the shared
block declaration metadata. Ordinary aggregate declarations, raw destination
allocations, by-value parameter copies and actual copy-result allocations issue
that evidence. Synthetic symbolic result blocks and constructor proof-entry raw
markers do not. The metadata participates in snapshot identity and joins.
The layout checkpoint introduced resource semantics version 71; the current
designation and checked interface semantics use version 75. This metadata grants no access.
C++ declarations and explicit child boundaries now additionally
retain their checked nominal identity. Embedded-record boundaries retain parent
relationships, root-relative offsets, full extents including padding, and
alignment. Layout metadata alone does not establish active lifetime or authorize
base-class-specific operations.

The implementation sequence is:

1. **Delivered prerequisite:** retain the declared layout of actual complete aggregate storage independently
   of cells, values and initialization, just as automatic scalars retain their
   declared type. Allocation/declaration and by-value object materialization
   supply this metadata. Raw footprint markers, ownership, and selection of a
   desired construction destination must not manufacture it. Stores and value
   havoc preserve it; incompatible declarations cannot be combined at a join.
2. **Structural selection delivered:** preserve explicit
   embedded-record boundaries alongside flattened scalar leaves through shared
   C layout lowering, including imported C++ records. The flat pre-order list
   records parent indices and complete-object-relative extents; it is derived
   from declarations, never dotted leaf names. Matching scalar leaves or fitting
   inside a parent allocation is not evidence that a child of the requested
   type exists there. Constructor binding checks the complete declared layout
   or an explicit child boundary and its projected layout. Indexed lookup limits
   work to the selected block, candidate boundaries and selected child contents.
   Nominal C++ identity and pointer designation remain separate obligations.
3. **Bounded input/member path implemented:** carry checked input designation
   through pointers and modular calls. A scalar
   input cannot acquire a live integer object merely by pointing into padding.
   This is the same domain boundary required by the sibling-pointer defect,
   not a constructor-only exception to the memory-read rules.
4. **Matching entry/call requirements implemented:** source entry records native
   scalar and aggregate object inputs separately from raw storage. Calls discharge
   those requirements from authenticated declarations or retained input domains.
   They do not fix the unknown extent of a constructor's containing allocation.
   Selection and initialization completion remain separate transitions.
5. **Bounded padding rule implemented:** combine authenticated destination and
   scalar-input witnesses with checked separation from every complete value
   field. The composition lookup selects owned members through their block
   indexes, supports distinct receiver/input blocks, and refuses reused members,
   views and mergeable string-literal ownership. The cross-block query retains
   at most two matches per side and checks at most four candidate pairs; a miss
   leaves separation unproven. Complete raw footprints and padding remain
   unwritten. The unchanged constructor and scalar-unwind integration tests,
   all four original cleanup Markdown fixtures and `basic-cpp` passed the
   preceding constructor-input checkpoint. Their integrated designation checks
   remain required before this stabilization work is complete. Preserve these
   and the hostile padding, alias, missing-write and no-op cases as coverage.

Do not silently add full-extent separation as a stronger contract precondition
or derive it from field ownership. It must follow from admitted object-domain
rules with caller evidence. Exact result/frame claims remain the acceptance
target. Declaration metadata alone remains insufficient: the repair also requires
checked scalar/record input validity and complete-width separation, with the
same requirements at symbolic entry and actual calls.

The recommended boundary keeps permission, object validity and initialization
as separate shared facts. Native declarations, references and other admitted
interfaces should supply exactly the validity facts their language semantics
justify, with matching checks at actual calls. Explicit contract notation is
needed where those native guarantees are insufficient, especially for raw
storage. This is not a choice between requiring extra annotations everywhere
and making byte ownership create a live typed object.

The remaining audit must identify which current native contract forms justify
which object-validity assumptions and how callers discharge them. Preserve
ordinary sidecar syntax when its native meaning already supplies the necessary
guarantee. If an interface genuinely needs a new validity precondition, report
it and update the contract openly; do not describe a proof under a stronger
precondition as the old theorem. Never infer initialization just from validity
or permission.

### Native interface audit and surface syntax

The shared model does not require a new keyword for each internal fact. Native
operations should supply checked evidence, and ordinary contracts should retain
their existing spelling where that spelling already expresses the requirement.
The bounded input/member implementation retains the following evidence; the
remaining paths still need their own admission and call checks:

| Current path | Evidence retained now | Remaining obligation |
| --- | --- | --- |
| C++ scalar/record reference parameters and receivers | Separate semantic input requirements; matching symbolic-entry, body, summary and certification checks; nominal record identity and explicit member paths | Extend only with checked evidence for additional source profiles and full pointer-result effects |
| Rust reference parameters (`rust/lowering.rs::lower_function`) | Pointer carrier, qualifiers and source reference/array/slice information in lowering | Carry the applicable Rust referent guarantees to shared checking without treating raw pointers as references |
| C and C++ raw pointer parameters | Pointer value and access type; admitted C++ raw inputs also carry an unresolved native identity even without a range clause | A signature alone does not establish a live pointee; checked native promises are required for traversal, and forwarding alone must preserve the unresolved identity |
| Memory `owns`/`views` clauses (`surface/lowering/resource_lowering.rs`) | Permission, range guards and snapshot-relative loadability; selected declared scalar and record prefixes retain separate native input requirements | A prefix promises a minimum extent, not a complete array; C character-byte clauses do not declare uint8 objects, and byte ownership or successful loads alone do not establish designation |
| Native callback members | Declared record member selection retains the exact function-pointer signature as its access type | A field's storage type does not certify a callback contract, byte reinterpretation or call authority; incompatible signatures refuse |
| By-value aggregate parameters (`kernel/functions.rs`) | A fresh copied destination with its declared layout | Check the source value against its actual object and preserve nested boundaries; do not use the requested layout to create source evidence |
| Constructor body entry and binding | Separate nominal record and scalar input requirements; checked complete/embedded selection, raw footprint, alignment and field permissions | Keep validity, permission and initialization separate; validate the unchanged RAII acceptance cases |

The pending parts of this audit describe missing evidence, not assumptions that
callers already satisfy. `with_contract_interface_argument_views` also supplies broad views for
evaluating contract expressions; those evaluation views are not evidence that
an arbitrary typed pointee exists. Neither those views nor a cast can establish
object validity.

Reference syntax must not be used as a blanket initialization rule. C++ can bind
a reference to an uninitialized scalar; the later read still needs an
initialization check. Rust references carry the validity requirements of their
referent type, and a type such as `MaybeUninit<T>` deliberately differs from `T`.
That distinction does not imply initialized padding in either language. C++
construction phases and limited uses outside an object's lifetime also need
operation-specific treatment rather than a universal fully-constructed premise
on every reference carrier.

The bounded interface now preserves native requirements as internal metadata,
checks them at calls, and uses the same requirements at symbolic body entry.
This includes body-independent summaries and direct execution; later profiles
must preserve that parity. A native
source signature, an explicitly checked contract requirement, or a justified
object operation may supply evidence; the prover may not invent it from a
successful typed cell lookup. Existing contract spelling should be reused only
where its documented meaning supports that requirement. Explicit raw-storage
predicates or operations remain possible if a concrete interface cannot express
what is needed; no new reserved keyword is selected by this design.

## Stabilization work and exit criteria

Pause expansion of the C++ feature profile for the following work. Keep changes
reviewable and preserve all existing source fixtures. These are completion
conditions, not a promise of a fixed number of PRs.

1. **Record the admitted operations and their evidence.** Audit the selected
   scalar, field, span, construction, assignment and byte-access paths against
   the state and operation tables above. For each, identify where type, access
   domain, lifecycle, initialization and authority are checked. Resolve missing
   evidence in the shared operation or narrow admission with a regression;
   surface any actual source-profile choice before proceeding past it.
   The confirmed member-pointer defect requires checked designation across
   arithmetic, loads, copies and calls; it cannot be closed by a documentation
   note or a syntax-only rejection of the initial probe.
2. **Selected representation bridge delivered.** The declared-uint32 law is
   shared by execution, logical observations and checked modular value reasoning.
   The exact value claim in
   [`modular_byte_output_word_value_requires_representation.md`](../mdtests/modular_byte_output_word_value_requires_representation.md)
   is now positive without changing its C or contracts. Ordinary, expanded and
   retained checks, hostile premises and indexed scaling pass. This closes that
   prerequisite, while other representation/frontend profiles remain bounded
   by their separate evidence requirements.
3. **Close lifecycle and call-path inconsistencies.** Check proof-entry naming,
   scalar initialization, constructor completion, copy materialization, havoc,
   branch joins and cleanup against the common laws. Reuse passing tests where
   they already demonstrate the obligation; change implementation only for
   demonstrated gaps. Legacy frontend placeholders must remain unavailable as
   general initialized-object evidence.
4. **Demonstrate consistency and bounded cost.** Complete the acceptance matrix
   below using the existing proof modes, hostile-artifact tests and deterministic
   work measurements. Include unrelated-memory growth to catch global scans.
5. **Resume the selected unchanged decoder proof.** Keep its exact byte-to-word
   result and span bounds, initialization and backing-lifetime claims. Record
   source/profile/dependency coverage and update the C++ issue. Any remaining
   algorithmic proof work should use this model rather than invent new object
   semantics for that helper.

| Obligation | Positive witness | Required negative/boundary witness |
| --- | --- | --- |
| Representation coherence | Typed store to bytes; four byte stores to declared word; partial byte update | Wrong type, incomplete bytes, stale snapshot, unsupported representation |
| Modular coherence | Inline and body-certified modular byte writer establish the same exact word | No-op/hole writer; value proposition or ownership without initialization |
| Destination and copy | Nested destination forwarding; lvalue copy; separate RHS assignment | Rebound destination, missing field, copied self-pointer wrongly rebased |
| Aliasing and frames | Contract-permitted aliases; checked separation; sibling/backing preservation | Freshness inferred from construction; lost or fabricated separation evidence |
| Lifetime and availability | Existing RAII, full-expression retirement and Rust move/drop witnesses | Dead temporary access; use after Rust move; destruction consuming independent backing |
| Access justification | Admitted scalar/subobject/array and authenticated `std::byte` access | Same-sized fake enum, cast-created object, unjustified cross-subobject arithmetic |
| Proof modes and trust | Ordinary, expanded and retained proofs of the selected source fixtures | Mutated destination/layout/type/effect metadata; older semantic identity |
| Scaling | Selected object/range work with growing unrelated memory | Heap-wide byte expansion or proposition scanning for a local operation |

The milestone is complete when every selected operation has an identified
semantic justification, these witnesses pass, and the unchanged decoder uses
the shared model with its original claim. C and Rust must retain their existing
construction, initialization, resource and lifecycle regressions; use paired
cross-language witnesses where the underlying operation is shared. Do not create
duplicate tests merely to populate the table.

This is a finite stabilization target: the representation bridge, checked
pointer designation for the admitted profile, an audit of the remaining
boundaries, and correction of demonstrated inconsistencies. The audit established
that pointer designation is a second concrete shared semantic gap; the earlier
estimate of just one known bridge was incomplete.
It is not a promise that all of C++ can subsequently be added without kernel
changes. Ordinary helpers within this profile should require contracts, proofs
or importer coverage. A feature that introduces a genuinely new object behavior,
such as replacement in live storage or overlapping union members, must explicitly
reopen the relevant design boundary before implementation.

## Alternatives not selected

- **A canonical byte blob for all memory.** It does not explain pointer
  provenance, object existence or legal access, and eager byte expansion harms
  scaling. Typed cells with coherent observations meet this milestone.
- **A C++-specific second memory model.** It would duplicate call, resource,
  snapshot and proof-checking semantics while leaving C and Rust inconsistencies.
  Language-specific admission over shared operations is the intended boundary.
- **Initialization inferred from mentioned reads.** This lets a proposition
  create the state needed to make itself meaningful. Explicit checked effects
  preserve the distinction between initialized unknown output and asserted values.
- **Per-decoder reconstruction intrinsics.** They conceal the missing relation
  between ordinary typed and byte observations. Derived lemmas remain useful;
  helper-specific semantics do not establish a stable object model.
- **A universal lifetime/alias policy for all three languages.** It confuses
  C++ construction and moves, C object access, and Rust availability/borrowing.
  Shared machinery must preserve those differences.
