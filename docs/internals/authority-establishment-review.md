# Object-anchored population authority

This records the implemented lifetime protocol for population authority, the
only population semantics. Its base case is an exact unary population
established in the storage creator's execution proof. A field-free resource with a private owned-memory
body can be folded to create one member and unfolded to consume it while
matching authority is owned. Opening an existing member temporarily exposes
its body without changing membership. Current `count(R(p))` reads the checked
total only with that authority. Retirement requires zero members. Verified
ordinary C helpers may borrow and return the same exact authority and member;
their standalone proofs receive an opaque population with no known count or
creator right. An imported member can be opened to use its private owned-memory
body, then closed before return. The helper does not need a concrete caller
allocation in its standalone proof; the caller established the member against
live storage before transferring it. A verified helper may create or consume
one imported member while returning its authority, including a private
owned-memory body. Creation consumes exactly the body's ordinary owned memory
clauses and produces the member; consumption consumes the member and produces
those same memory clauses. The standalone proof checks `fold` or `unfold`, and
the concrete call updates the caller's population under transferred authority.
Certification requires that check: a declared consumption of an exact member
whose population the helper governs must appear as a recorded death at its
exit. A helper that receives the member and does not spend it is refused,
whether it holds the authority directly or through a borrowed control.
Otherwise its caller would apply a death that never happened, and a returned
control would state its counter equation before that death.
Creation also checks that the caller's anchor is still live. An ordinary
field-free `control(p)` may now own both the counter cell and
`authority(reference(p))`, with a fact equating the cell to the current count.
Its direct proof can fold, open, close, and unfold that body. A checked ordinary
helper can borrow and return the folded control while creating or consuming one
reference. The helper entry imports an opaque symbolic count only from that
exact wrapper and its counter equation; the caller's concrete ledger tracks
the member exchange across the call. Selective verification may use the scoped
contract of a concrete helper whose proof is outside the selection. Arbitrary
external contracts, worker calls, and field-bearing or nested member bodies
remain refused by this slice. The modeled mutex operations are the exception
among C calls: they transfer an authority-bearing control without changing
any population, as described in the
[mutex contract page](mutex-resource-contracts.md#authority-bearing-controls).

Shared-parent helpers combine these transfers with ordinary named memory
resources. A parent instance owns its link field; a reference is a separate
companion capability, and child control remains a single explicitly transferred
resource. The checked helper transfer selects its member creation or consumption
independently of the order of companion clauses. Borrowing one reference and
producing another preserves the borrowed reference and increases the total by
one. A returned control exposes its invariant at the updated population state.

An empty member family also supports a checked quantity exchange such as
`consumes 2 of reference(p); produces reference(p);`. Call admission requires
the whole consumed quantity from the caller's custody, including units held
as separate facts. Independent helper certification checks the declared net
population change, and the return partition checks the produced custody.
Historical arguments are matched to the consumed population's authenticated
identity before returning members to the caller. A global count never supplies
missing owned units. The `authority_two_to_one_quantity_*` fixtures cover the
exchange and its rejection cases;
`holder_drop_exchanges_two_separately_held_references.md` admits that quantity
contract at a call whose caller holds the two units as separate facts.

A function boundary retains the resource bindings checked at entry. If C clears
`p->kid`, a borrowed `reference(p->kid)` still returns the reference actually
received; it is not evaluated again against the cleared field. Entry observations
remain historical, and current observations use the checked exit population.
Folding an ordinary named memory resource retains the pure body facts checked
at that state, including facts transported across a disjoint helper call.
It does not retain the body's exclusive memory ownership as a separate resource.

The nested-overconsumption fixture checks that a consumption beyond the
declared one is rejected as missing ownership.

The supported contract shape uses only ordinary resource clauses:

```text
authorized resource reference(p: int32*) { owns p[0..1]; }

int32 acquire(int32* p) {
    owns authority(reference(p));
    consumes p[0..1];
    produces reference(p);
}

int32 release(int32* p) {
    owns authority(reference(p));
    consumes reference(p);
    produces p[0..1];
}
```

The listed memory clauses must equal the complete private body, including
each owned range when there is more than one. Neither helper establishes a
second authority or gains unlisted memory.

## Allocation companions across helpers

An ordinary checked allocation input also transfers its storage cleanup custody.
This applies to heap parents that own their link cell and pass
`allocation(p, sizeof(struct parent))` separately; the allocation need not be
inside an authority-bearing control. Borrowed storage returns its custody with
the resource, while a consuming helper may reclaim it after the usual ownership
and population-cleanup checks. The transfer keeps the original creation event:
receiving allocation ownership does not let a helper establish new authority.
The kernel uses the authenticated allocation input and its indexed lifetime
anchor, rather than inferring this permission from arbitrary owned memory.

## Establishment and uniqueness

A population is anchored to the lifetime of a C object appearing as an argument
of its resource type. The initial slice is exact unary `reference(p)`.
Authority may be established only in the execution environment that actually
creates the storage, while that environment owns the anchor. Each population
scope may be established once during that storage lifetime. Establishment
creates an empty population; creating its first member is a separate checked
transition. Receiving ownership of existing storage does not grant permission
to establish authority, even when its population has never been registered.

Registration belongs to the anchor lifetime, not to the current local proof
context. Passing the anchor to another owner preserves its registrations even
when the authority remains with the original owner. Neither local absence of
members nor recovery of raw memory ownership permits duplicate establishment.
Aliases must resolve to the same anchor lifetime and registration. Reuse of a
C address after deallocation must resolve to a new lifetime.

The C bridge preserves this registration through ordinary verified helpers,
checked authority-bearing wrappers, and disjoint parent frames. Thread
transfers still need checked integration.
Minting a fresh internal identifier whenever a pointer is encountered would
violate this rule. The abstract kernel allocator
creates fresh abstract lifetimes only; it grants no C memory permission and is
not a source-level authority constructor.

Establishment must also precede any member creation for that population. The
creation environment alone does not prove emptiness at an arbitrary later
point: it might already have produced and transferred ordinary `reference(p)`
instances. The source slice checks production and consumption of one field-free
member with a private owned-memory body at a time, exchanging that body and the
owned member fact while changing the exact total in one certificate event. Its
creation ledger retains per-family member history, so local absence
after consumption or future transfer cannot justify re-establishment. Other
member forms still require checked integration.

## Membership and cleanup

Only the authority holder may observe the exact total, create members, or
consume members. Consumption additionally requires owning the members being
consumed. Transferring members needs their ownership but does not need authority
and does not change the total. Authority can be transferred independently of
members and anchor ownership.

Checking the current facts of a folded control uses a temporary owned-body
projection. The kernel authenticates its exact owned head and contained
authority, removes that head and the observations supported by its occurrence
from the projection, then composes the checked private body. Lowering and
memory-dependency checks use this same projection. The live folded resource
remains unchanged until its separately checked resource exchange. An unrelated
unbound view still fails the dependency check, even beside owned memory; an
ownership observation grants no stable-view loan.

Closing an open control authenticates the children currently owned, rather
than trusting the suspended head's invariant. Its local projection retires
only that head's supported observations and reuses the checked children for
custody reads. It publishes no body facts: the current invariant, including
the counter equation, must still follow from the explicit facts and ledger.

Function exits account for all returned exclusive units jointly, including
borrowed survivors. One exclusive unit cannot satisfy both a borrowed return
and a produced return. The kernel checks actual body ownership and allocation
lifetime before accepting the effect. An inactive guard contributes no units;
an unresolved guard does not certify a resource transition. Smart closers and
explicit assumptions retain the same checked resource evidence, so their
presentation spelling grants no additional transfer permission.

Retirement requires authority and a zero total. It removes the live authority
but retains the fact that this scope has already been established until the
anchor lifetime ends. Re-establishment during the same lifetime is forbidden,
including in the original creating environment. Outstanding members prevent
retirement. A new actual allocation, even at the same address, has a new
lifetime and may establish its own authority. The anchor cannot be freed while
any authority remains registered. Scope exit cannot silently discard authority, members, or anchor
ownership. Moving these obligations to another owner is allowed.

An exact count read selects the already-owned population authority of its
anchor as written. Lowering does not respell the anchor through a proved
pointer alias; a proof that counts through an alias rewrites it to the anchor
first. The selected authority is authenticated against the live creation
ledger. Pointer equality supplies neither authority ownership nor membership
permission. The regression covers an alias that is refused, missing ownership,
an unauthenticated authority head, and increasing unrelated authority contexts.

A closed control resource packages authority along with its counter ownership
and invariant. Opening that ordinary resource exposes the permissions needed
to change membership and counter together; closing must reestablish its facts.
The authority-mode resource-rewrite checker now validates this exact
memory-plus-authority exchange and rechecks the body fact against the current
ledger total. Its supported shape is field-free, unconditional, and has one
contained authority plus owned memory. A control may instead declare proof
fields, making it a named instance that a mutex can hold. Its fold and unfold
use the ordinary named-instance exchange: the fold consumes the caller's
actual authority, an unfold returns the one the instance holds, and the
certificate checker requires the creation ledger to be unchanged. An unfold
also requires the authority's population to be recognized. A standalone
helper therefore cannot yet open an imported field-bearing control, and an
authority already owned beside the control cannot be duplicated by opening
it. Other wrapper bodies remain future work.

## Syntax and staged implementation

The intended resource expression remains `authority(reference(p))`, composed
using ordinary `owns`, `consumes`, and `produces`. No new keyword is selected.
The existing `construct` operation creates abstract tokens under an outcome
contract; it does not establish the lifetime or registration evidence above.
The proposed reuse of `construct` has not been adopted. The selected source
operations are `fold(authority(reference(p)))` for empty establishment and
`unfold(authority(reference(p)))` for zero-count retirement. These reuse the
existing tactic syntax and record a dedicated checked certificate event.
Ordinary `fold(control(p))`, `open(control(p))`, and `unfold(control(p))` now use
the checked resource-body exchange for the restricted shape above; folding
cannot establish or duplicate authority.

Independent authorities must never count overlapping sets of members.

## C creation events and explicit helper contracts

For heap storage, the creation event is successful resolution of an actual
`malloc` (also `calloc` and `realloc(NULL, size)`); allocation failure grants
nothing. The originating invocation is recorded when allocation is initiated:
a helper that merely tests the pending result cannot become its creator.
Successful resolution uses that recorded origin even across a call.
Successful reallocation of existing storage ends its old lifetime,
so it must first satisfy the same authority-retirement obligations as free.
The initial bridge must withhold establishment permission for that case until
its checked retirement/creation transition is implemented. For automatic storage, it is the
execution of the object's declaration. A copied pointer is an alias, not a new
object. Re-entering a declaration after its prior lifetime ends creates a new
lifetime. Global storage needs a startup proof environment before it can use
this rule; ordinary function entry must not re-create global authority.

The creator establishes empty authority before calling an initializer. The
initializer receives that authority explicitly through its ordinary resource
contract and uses it to create the first member. The current narrow helper
rule covers a member with a private owned-memory body when the contract
transfers that body explicitly; this example also needs wrapper transfer. A helper that receives only
memory or `allocation(p, size)` cannot establish authority. The earlier
allocation-custody proposal is superseded; authority need not retain the heap
allocation resource, and this design does not restrict anchors to heap objects.

For example, the intended initializer interface uses existing contract clauses
(its wrapper transfer remains to be implemented):

```text
void object_init(struct object* p) {
    consumes allocation(p, sizeof(struct object));
    consumes *p;
    consumes authority(reference(p));
    requires count(reference(p)) == 0;
    produces control(p);
    produces reference(p);
}
```

Here `control(p)` packages the allocation, memory, authority, and counter
invariant. Its allocation ownership serves ordinary eventual deallocation;
it does not justify establishing authority. The caller must obtain authority
at the creation site before invoking this helper. The original C need not
change. The creator uses the checked authority `fold` operation before the call.

The concrete bridge points are successful `resolve_pending_heap_allocations`
and real `declare_local` / `declare_aggregate_local` events in
`src/kernel/eval/statements.rs`. `with_heap_allocation_claim` in
`src/kernel/primitives/memory_state.rs` imports a claim about existing storage
and grants no creation permission. Generic `with_block` is also insufficient:
it creates verifier-generated parameter slots and other synthetic storage.

A distinct invocation identity must distinguish caller and callee, even if
neither needs address-backed parameter slots. Existing `next_local_frame` is
not such an identity. Calls preserve population registration and transport
explicit authority, while retaining unspent creation permission in its
originating environment. Returns restore the caller's environment. Direct
free, scope exit, and contract retirement must reject live authorities before
ending the anchor lifetime.

The abstract kernel checks the creation-environment and once-per-lifetime
restrictions. A separate C event ledger records successful heap creation and
actual automatic declarations, uses distinct caller/callee environments, and
clears provenance on direct free, scope exit, and checked contract retirement.
It retains per-storage family history: once a member existed, transferring it
away cannot make later establishment appear empty. Pending heap outcomes carry
that history to the resolved allocation. The first query accepts an exact heap
or automatic-object base; subobject/interior anchors still need checked
canonicalization. Its opt-in is enabled only by an authority-mode source proof
or kernel test. Checked member operations and verified sequential helper
transfers update this history together with resource custody.

The source parser recognizes `authority(R(p))` for an exact unary, field-free,
pointer-anchored declared family, and lowers it to a distinct exclusive kernel
resource. Ordinary resource evaluation refuses to mint it. The explicit
project mode and proof artifacts carry the semantics choice. Checked source
`fold`/`unfold` establish and retire authority; direct `fold(R(p))` and
`unfold(R(p))` create and consume one field-free member, exchanging its private
owned-memory body. The exchange requires matching owned authority and is
rechecked by the certificate checker. `open(R(p))` exposes that body while
preserving membership, and its close restores the body. Current exact
`count(R(p))` reads the ledger. A verified
ordinary helper can borrow and return the same authority and member through
the checked resource contract and creation ledger. Raw authority imports only
the declared custody; it supplies no arbitrary exact entry total. A checked
control invariant tying a C field to the count supplies an opaque entry total,
with a certified lower bound from the members owned on entry. Initialization,
retain, and conditional release apply their checked changes to that total.
Contract states retain the entry total, and checked empty retirement retains
an immutable final zero without restoring update permission.

An exact member with a private owned-memory body may be born or spent under
imported authority when the opposite contract side transfers its entire body
using ordinary `consumes` or `produces` clauses. The same population update is
applied to the caller's concrete authority at a verified call. The sequential
refcount project exercises initialization, individual and symbolic-batch
updates, allocation failures, and final reclamation. Shared parents,
field-bearing and wildcard populations, the bounded pool, mutex-held controls
and workers build on the same rules
([worker authority protocol](worker-authority-protocol.md)).
