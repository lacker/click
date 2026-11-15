# Aggregate construction and return destinations

This records the implemented shared aggregate construction and return-destination
contract.
The shared kernel supports a bounded complete-object construction return mode.
Existing C aggregate returns remain field copies. C++ now admits bounded
returned construction and forwarding under a body-validated copy-equivalence
restriction. Assignment uses a distinct RHS temporary and full-expression
retirement. The unchanged pinned `SpanPopBack<int>` and its read/write callers
verify under the bounded profile below.

The copy-return implementation now checks source initialization inside the
materialization transition, before allocating or copying a result. Kernel tests
also exercise an explicit destination through two nested procedure calls,
including its self-pointer and ownership transfer.

The shared memory model can also describe initially unwritten symbolic
storage without claiming that it is fresh or separate from arguments. Actual
writes establish initialization; resource naming does not. Initialization
survives value forgetting, intersects across branches, and follows checked
pointer equalities. Construction-return proofs use this initially unwritten
storage, with ownership supplied separately by their entry contract.

Caller allocation now has a separate `c_allocate_aggregate_destination`
operation. It allocates fresh automatic storage and its byte ownership without
seeding field values. Re-declaration uses the existing retirement and fresh
generation checks. Ordinary aggregate/array declarations and the existing Rust
constructor placeholder protocol retain their behavior. Automatic scalar
declarations now create exact byte ownership through the shared allocator,
independently of initialization. C++ direct local constructors now use raw
destination allocation.

`CAggregateReturnMode::Construction` now binds the hidden result to exact call
metadata before body execution. Completion validates the same pointer, layout,
live storage, and initialized value fields. Direct calls, forwarding calls, and
body-certified modular summaries share that destination; completing a result
does not allocate or copy. The initial kernel slice requires complete-object
storage, an explicit byte owner, and ordered non-overlapping scalar fields.
Construction returns still require complete-object destinations. Union/array
layouts, exceptional construction, external void-constructor assumptions, and
constructor callbacks remain refused. Explicit external construction-return
contracts may assume that the selected caller-owned result is completed with
initialized value fields. These are reported external assumptions, not body
certificates, and do not grant initialization to ordinary output buffers. Contract
matching, state substitution, branch joins, and checked state comparisons
include the destination and result mode. C++ source admission uses the bounded
copy-equivalence restriction below.

Ordinary void constructors can designate a pointer parameter as their
construction destination. The call binds its entry value once; reassignment of
the parameter cannot replace the object checked at completion. The body must
initialize every modeled value field, and only a body-certified summary can
establish that initialization at a modular call. Native constructor contracts
need write authority for the fields, not padding. C++ constructor lowering and
Surface entry setup preserve this metadata and start with an unwritten symbolic
object footprint. This footprint does not fix the containing allocation's size;
field liveness comes from the entry contract. At a call, constructors can select
an aligned subobject within a known parent allocation. Completion and summaries
initialize only the child's fields, preserving the parent's extent and sibling
storage. C++ member-initializer lists now lower embedded construction to these
checked child calls, within a public non-default `noexcept` constructor profile.
Definitions may come from the selected file or locked header dependencies;
Clang-resolved non-explicit constructors and checked read-only scalar initializer
calls are supported. Children require trivial destruction. Neither
the native signature nor sidecar syntax changes.

`c_end_automatic_lifetimes` makes a frontend-recorded expression boundary an
explicit shared statement. It uses the existing automatic-storage retirement
checks, removes only the named objects and their ownership, and preserves copied
pointer values and independently live backing storage. C++ lowering records and
emits full-expression retirement for admitted assignment temporaries.

## Scalar initialization

Scalar declaration construction also has a checked initial-value transition.
`c_declare_initialized` allocates fresh automatic scalar storage and its exact
byte ownership, evaluates the initializer, checks its native conversion, and
writes the initial value. A read-only scalar is then frozen in both its local
binding and its allocation metadata. Freezing preserves the declared type,
extent, allocation generation, initialized cells, and ownership; even an
unqualified alias cannot write that allocation. Ordinary assignment has no
initialization privilege. There is no reusable operation that can initialize a
read-only object again after forgetting its value.

The declaration initializer participates in expression traversal, substitution,
address-taken analysis, and checked execution certificates. Reading an unwritten
initializer input still fails. Scope retirement and redeclaration retain the
existing generation checks, so initialization cannot revive a stale address.

C admits initialized read-only automatic scalars, including native pointers.
C++ admits supported integer and fixed-byte enum `const`/`constexpr` locals;
qualification remains on the object, while lvalue-to-rvalue conversion produces
the corresponding unqualified scalar value. A captured helper result initializes
the source object after the checked call, using a distinct mutable capture.
Read-only initializer calls must be context-independent: the checked call graph
tracks constant-evaluation observations, including nested calls and cached
subgraphs, and refuses them in these initializers. Closed compiler constants
retain their existing checked profile; unrelated runtime observers are unaffected.
Initializers that observe their own not-yet-bound destination through a call,
const automatic aggregates/arrays, and general constant evaluation remain outside
this bounded frontend slice. Existing Rust MIR assignments retain their current
rules; the shared construction operation is available without introducing C++
mutability or borrow rules into Rust.

## Surface and source boundary

Keep native result signatures, `result` field projections, and existing
`owns`/`views` clauses. A hidden destination is execution metadata, not another
source parameter or a user-managed resource. Users must not name compiler
temporaries, allocate return slots, or add tactics to retire those slots.

The shared construction-return mode now lowers to an implicit owned byte range
for the complete result object at entry and exit. Trusted frontend entry setup
supplies an arbitrary symbolic destination and its input ownership; the actual
call still has to supply that ownership. Binding the destination adds no
freshness, separation or write authority. The returned owner has a generated
resource claim checked from execution, independently of the written value
postconditions. Returning ownership does not initialize fields.

Field-address expressions retain the field's pointer type rather than the
aggregate storage's byte-pointer carrier. This lets the native self-pointer
contract use `&result.value` without a cast or new syntax.

Before C++ admission, exercise `result.self == &result.value` through ordinary,
expanded and retained verification. Reuse existing address-expression syntax;
if aggregate result field addresses need lowering support, add that support
without introducing a new construction clause. Address formation checks live
storage and qualification, not field initialization or read authority.

## Operations and storage identity

The shared engine distinguishes allocation, construction, copying and retirement.
Frontend evidence selects the operation; the kernel checks its transition.

| Operation | Required evidence | Result |
| --- | --- | --- |
| Allocate storage | Checked size, alignment and allocation event | Fresh storage identity; no initialized field values |
| Construct into a destination | Exact destination, compatible layout, valid lifetime and write authority | Same identity, with the fields actually initialized by execution |
| Copy an aggregate | Initialized readable source fields and writable destination fields | Copied field values; pointer values are not rebased |
| Forward a construction destination | Compatible result interface and the same checked destination | No allocation, copy or additional ownership |
| Retire a temporary | Its recorded language lifetime boundary and required cleanup | Only that temporary's storage expires |

An address is allocation identity plus byte offset. Equal layouts do not make
objects identical. A subobject destination does not resize or replace its
containing allocation. Constructing into existing storage is not an allocation
event and cannot establish separation from arguments or other caller storage.

The first source slice uses fresh complete-object storage and forwarding of
that storage. The shared validation must still reject forged freshness and
unjustified separation when a supplied destination aliases an argument. Valid
overlap is judged by the actual reads, writes and resource transfer, not a
blanket rule that destinations cannot alias. Reuse of an already-live object's
storage requires explicit lifetime/replacement semantics and is not silently
admitted by this slice.

## Shared interface

Extend `CFunctionContractInterface` with an explicit aggregate result mode:
existing field-copy result or construction result. Keep the aggregate layout
and native result type. Include the mode in exact interface matching, callback
compatibility, hashes and retained proof identities. A certificate for one mode
cannot implement the other. C and Rust continue selecting their existing mode.
The mode specifies result storage, not a ban on copying inside a function:
a destination-return body may explicitly copy an existing value into its result
destination when its source semantics require that copy.

Represent the actual destination on the call execution, not on a reusable
function definition. It carries the exact pointer, selected layout, lifetime
owner and checked storage/authority evidence. Construction calls require this
binding; ordinary field-copy returns retain their existing fresh materializer.
Do not encode the destination as an ordinary user argument that could be
substituted independently of the result contract.

For body verification, introduce a symbolic destination constrained only by
the construction interface's checked preconditions. The callee constructs
there. At each call, instantiate that symbolic destination with the caller's
actual object, including alias relations with evaluated arguments. Bind
postcondition `result` to this same destination after successful completion.
Do not use the existing fresh `PointerBlock::Temporary` result for this mode.

Ordinary execution, modular summary application and retained checking must
consume the same destination relation. Expansion serializes enough evidence
to reconstruct it. A proof cannot change the destination, mint storage while
binding `result`, or restore a retired allocation. The caller supplies storage
authority once; nested forwarding transfers and returns the same authority.

Keep destination allocation separate from function effects. A fresh result
object's authority originates at caller allocation. A modular callee summary
must describe the constructor's actual writes, initialization and other
effects; it cannot obtain a general write frame from the presence of a result.

## Initialization and failure

Complete construction requires initialized values for all modeled value
fields, not necessarily padding bytes. An early field address can be stored
before the field's value is written. Observing the field value still requires
initialization and read authority. Copying a pointer never grants authority
over its pointee.

The legacy `DeclareAggregate` constructor kind seeds scalar
placeholders so current constructor contracts can use the existing cell
machinery. Its frontend overwrite obligation is not a completion certificate
for the new result mode. The implementation must distinguish actual completed
initialization from these placeholders, using the existing initialization
machinery where possible. Do not publish a successful construction result
merely because symbolic cells exist.

On validation failure there is no accepted transition or completed result. On
a represented runtime failure, retain already-executed effects and the exact
initialized portion; do not roll them back or publish a fully live value.
Required cleanup belongs to the selected language's lifetime protocol. The
first C++ profile admits nonthrowing constructors with trivial destruction;
throwing/nontrivial construction stays refused until its cleanup transitions
are supported. Existing Rust move/drop behavior must remain unchanged.

## Returns, expressions and temporary boundaries

For construction returns, bind the destination before executing the body.
`return factory(...)` forwards that destination when the selected source
semantics justify it. Callee exit retires only callee-owned storage, not the
forwarded result. Completion checks initialization and binds the result;
there is no final field copy.

When source semantics require materialization, allocate a distinct temporary,
construct it, perform any explicit copy, and retire it at the recorded boundary.
Copying a self-pointer leaves it pointing into the source temporary. After that
temporary expires the copy may still contain the pointer value, but a read
through it must fail. A pointer into a separate caller backing allocation is
unaffected by retiring the descriptor that held it.

Initialization and assignment have different destinations. For example,
`span = span.first(n)` evaluates the returned descriptor with the old span
available, then performs checked trivial assignment. It must not construct
directly over the live left-hand descriptor as an unproved optimization.

## C++ admission evidence

The selected profile remains pinned LP64 C++20 with its existing Clang and
library inputs. Preserve the unchanged source and native extent types.

| Source case | Admission requirement |
| --- | --- |
| Direct local construction | Existing checked constructor destination |
| Copy from a live lvalue | Resolved trivial copy and checked layout; preserve pointer values |
| Prvalue factory result | Required result-object construction plus evidence accounting for any permitted trivial-class result temporaries |
| Forwarded factory result | Same requirements recursively, with exact destination forwarding |
| Named local return eligible for NRVO | Deferred until both permitted behaviors can be checked or the pinned compiled behavior is justified |
| Temporary followed by copying | Distinct storage, explicit copy and correct retirement |

Clang's expression category or an NRVO eligibility flag alone is insufficient
evidence of the selected execution. Before admitting each return shape, record
the language rule and compiler/ABI evidence that justify its transitions. If
multiple executions are admitted, prove the claim for each, or prove that their
observable behavior agrees for the selected claim. Keep the shape refused when
that evidence is missing. Do not infer address independence from trivial copying.

The first admitted returned-construction profile validates the resolved constructor
and its reachable value helpers from their typed bodies. Initializers may depend
on evaluated scalar/pointer arguments and constants, with embedded construction
checked recursively. They cannot read aliasable memory, expose their receiver or
local storage, or perform other runtime effects. Helpers remain ordinary
body-checked modular calls; read-only contracts alone do not establish this
restriction. Direct local constructors retain their broader existing profile.

C++20 `[stmt.return]` and `[dcl.init]` select the prvalue result object;
`[class.temporary]` permits additional qualifying trivial class result objects,
and `[class.copy.elision]` governs optional named returns. This frontend uses
field-value equivalence across permitted trivial copies for the bounded profile,
not an ABI-specific no-copy claim. Given the same evaluated argument values,
the admitted constructor writes the same modeled field values into either
object, and trivial copies preserve those values. No pointer derived from the
intermediate object's storage is exposed, so its retirement preserves the
contract. Padding and object representation are outside the admitted observation
profile. A shared checked regression constructs directly or through one/several
explicit copies and retirement, preserving the descriptor and external backing.

Artifact schema 52 distinguishes resolved returned construction, aggregate-call
forwarding, new-object initialization and assignment from a construction call. The
importer recomputes eligibility; no serialized eligibility flag grants access.
Source and signature validation still checks declaration identities, exact
nominal types, arguments, field order and cleanup. Named return candidates,
moves, user-defined copies, nontrivial destruction, mixed copy/construction
return branches and storage-sensitive returned constructors remain refused.
Construction-return functions require `noexcept` and no exit cleanup in this
slice. Existing `ReturnRecord` copy-only functions retain the copy result mode.
For assignment, the exporter requires a resolved trivial copy assignment with
an exact nominal prvalue call result materialized for the full expression.
C++20 `[expr.ass]` sequences RHS evaluation before assignment; `[class.temporary]`
ends the temporary's lifetime after the full expression. Lowering evaluates
arguments, allocates distinct raw RHS storage, calls the factory into it, copies
into the live LHS and retires the RHS. The lifetime event is derived separately
from the destructor inventory, because trivial destruction does not erase the
object's lifetime. Direct construction over the initialized LHS is never used.
References into independently live backing survive this retirement under their
existing authority. Move assignment, user-defined assignment and other temporary
shapes remain outside this slice.

The identity-sensitive `Node` is the shared-kernel test oracle. It is not a
universal source claim about trivially copyable C++ returns. The first real
target is the pinned span descriptor: its pointer refers to independently live
backing storage, so permitted descriptor copies should preserve the target
contract. Establish that from checked constructors/copies, not a span intrinsic.

## Delivery and acceptance

1. Freeze the existing copy-return behavior and the contract in this document.
   Kernel regression coverage distinguishes copied self-pointers from result
   identity and descriptor storage from backing lifetime. This stage does not
   admit new source or implement destination returns.
2. Add the shared result mode and checked destination binding together with
   body execution, modular application and certificate support. Test direct
   construction, forwarding through two calls, complete initialization,
   layout/identity substitution, missing authority, aliasing arguments and
   partial construction. No standalone unchecked interface flag is a delivery.
3. Add materialization and retirement at expression boundaries. Test explicit
   copy, dead self-pointers, live external backing and caller-owned storage.
4. Admit the bounded C++ forms with compiler evidence, source regressions and
   hostile artifact checks. Confirm existing Surface syntax on self-address
   postconditions and all three proof paths.
5. Verify unchanged pinned span construction, runtime `first` and `SpanPopBack`,
   plus modular callers that read and write the returned reference with their
   existing backing authority. Retain native uint64 extent and the accepted
   `1 <= N <= 1,073,741,823` single-range bound.

Pinned runtime `first(K)` now has ordinary, expanded and retained returned
construction coverage for `0 <= K <= N` within the accepted bound. Equal
endpoints require no stable-view loan, so a zero-count caller passes with only
descriptor views.

Unchanged Bitcoin v31.1 `SpanPopBack<int>` verifies for
`1 <= N <= 1,073,741,823`, with native uint64 extent, mutable descriptor fields,
an initialized backing view and descriptor/backing separation. Its pointer is
unchanged, its length becomes `N-1`, and the returned reference retains the
original last element's address and value. The entire original backing array
remains unchanged through assignment and RHS descriptor retirement. The proof
states current-array reads against entry-array reads, including the element
outside the shortened descriptor.

Modular callers read the saved reference using views, or write it using an
existing backing owner. The write caller establishes the new last value and a
frame for every other original element. Singleton callers construct an empty
RHS descriptor and then read or write the still-live original element;
three-element and symbolic-length fixtures also pass. Ordinary, expanded and
retained verification cover the helper and callers. Missing descriptor/backing
authority, nonempty and extent bounds, descriptor/backing separation, out-of-range
`first`, and views-only writes are refused.

Captured interior addresses retain one checked additive spelling per address
class for indexed supplier selection. This metadata preserves the explicit
base; it grants no authority or bounds. Alignment expands at most one retained
spelling per path, and deterministic multi-size tests cover unrelated owners in
the same address space. Separation may relate eight-byte descriptor fields to
four-byte elements: each access must fit its own certificate side in full.
Constant cross-width containment uses exact byte intervals; symbolic cross-width
containment remains refused.

Primary code owners are [shared interfaces](../src/kernel/primitives/contracts.rs),
[interface carriers](../src/kernel/primitives.rs),
[call execution and result binding](../src/kernel/functions.rs),
[statement execution](../src/kernel/eval/statements.rs),
[execution proofs](../src/kernel/proof/execution.rs),
[Surface contract lowering](../src/surface/lowering/annotations.rs), and
[C++ lowering](../src/languages/cpp/lowering.rs). The existing C++ identity
regressions live in [cpp_import.rs](../tests/cpp_import.rs).

Each implementation increment requires focused positive and negative tests,
agreement of ordinary/expanded/retained verification, and preservation of C
aggregate-copy/return and Rust construction/move/drop/scope-exit behavior.
Changed hot paths need deterministic multi-size work checks for destination
forwarding, field count and unrelated caller state. No whole-state scan or
larger tactic budget is an acceptable substitute. Use the repository's normal
local-check and CI gates and report exactly which checks ran.
