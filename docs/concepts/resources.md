# Resources and memory permissions

Resources are the logical objects that a proof can hold, view, transfer,
consume, split, combine, fold, and unfold. A held resource plus its `own` or
`view` access mode is a resource fact. Resource facts sit alongside pure facts
such as integer bounds, but obey resource-composition rules because owned facts
must not be copied freely.

A memory permission is the access authority provided by a memory resource
fact. Permissions are therefore one use of resources, not a parallel proof
state or a second general-purpose tracking system.

Click currently has two first-layer memory permissions:

<!-- verified-example: mdtests/resource_view_fact_unbound_fold_rejected.md -->
```click
views p[0..1];
consumes p[0..1];
```

These clauses create resource facts in the verifier's resource context. External C
memory accesses must be covered by the current resource context:

- a load requires a viewed or owned memory resource,
- a store requires an owned memory resource,
- automatic scalar declarations create ownership of their exact byte size;
  ordinary local access uses it without additional proof annotations,
- ordinary record declarations and construction destinations create ownership
  of their complete byte size, including padding, without initializing fields;
- legacy automatic arrays retain implicit local access.

Scalar allocation ownership is independent of initialization. It can be lent to
an ordinary helper contract and is retired when storage leaves its scope or is
re-declared. Folding or transferring the permission does not leave a second
implicit capability for direct local access.

## Resource context and families

Internally, Click represents resource facts as `ResourceFact` values. A
resource is the bare object being described, such as `memory(p[0..n])`; a
resource fact is that resource with an access mode, such as
`view(memory(p[0..n]))` or `own(memory(p[0..n]))`. Resource facts are what the
current resource context holds. A resource family defines the rules for a
group of related resources:

- when one resource entails another,
- whether an owned resource can be duplicated or discarded,
- how resources split and rejoin,
- what gets consumed by a function call or statement,
- what other resources are invalidated by consumption.

The main built-in resource family is memory. Its viewed and owned elements are
resource facts over a range. The context is not just a bag of pure facts:
`ResourceFamilyAlgebra` defines how each family validates, combines, transfers,
and consumes its facts.

The viewed element grants read authority over memory for a borrow. While that
borrow is active, the covered memory stays unchanged and stays allocated: no
component may store into it, free it, or end its lifetime. A view is temporary
stability, not permanent immutability.

The Click surface requests these elements with `owns`/`consumes`/`produces` and
`views` respectively.

An owner and a view of the same memory cannot sit side by side in one resource
context. Ownership satisfies a viewed requirement by lending: the owned element
moves into escrow for the borrow, and the lender recovers it when the borrow
ends. Lending is a checked transition. No entailment, normalization, fold, or
theorem turns a view back into ownership.

This resource-family boundary is intentionally more general than memory
ownership. Click also has exact-match user-defined resources, which can model
API protocols without forcing those protocols to look like heap cells.

## Viewability and authority

`viewable(...)` and permissions still answer different questions, but access
permissions include the viewability needed for the covered access.

`viewable(p[0..n])` says the range is viewable. It is about
memory safety and bounds.

`views p[0..n]` or `owns p[0..n]` says the current code has authority to access
that range. It is about permission.

For an external read, `views` is normally enough:

<!-- verified-example: mdtests/array_parameter_first_element_views_one_cell.md -->
```click
int32 first(int32 p[]) {
    views p[0..1];

    ensures result == p[0];
}
```

Similarly, an owned memory resource grants authority to store and makes the
covered range viewable. Use `viewable(...)` separately when you need to prove memory exists
without granting read or write authority, or when a larger structural bound is
useful for index reasoning.

When the same viewability fact must appear as a proposition, use
`viewable(segment)`. This is common in composite resource definitions, where
`fact` clauses are pure propositions rather than structural requirements. A
`let name: type where proposition;` clause binds an existential pointer for the
rest of the body, which is how a resource names a tail pointer packed into an
integer word; the language reference describes how fold and unfold bind it.

## Viewed memory

`views` permits loads. It does not permit stores. The covered memory is stable
for as long as the view is active, so repeated reads of the same cell produce
the same symbolic value: nothing that could change the cell is allowed to run.

<!-- verified-example: mdtests/viewed_cell_reads_stay_equal.md -->
```click
int32 peek(int32 p[]) {
    views p[0..1];
    ensures reads_agree: result == 1;
}
```

Here the C body reads `p[0]` twice and returns `a == b`; the two loads are one
value.

A `views` clause on a function is a shared borrow that lasts the whole call,
from the checked entry transition to the checked return transition, not to the
last load in the body. If a caller owns `p[0..1]`, it may satisfy a helper's
`views p[0..1]` requirement, and Click lends that owned element for the call.
The caller cannot write, free, or reallocate those bytes while the call is in
progress. The return recovers the owner and adds no new persistent view. A view
the caller already held is different: it remains in the caller's resource
context until explicitly transferred or consumed.

Stability excludes the conflicting access instead of comparing values
afterward, so a store of the value a cell already holds is refused like any
other store. Initialization, bytewise stores, deallocation, and the abstract
effect of an opaque call all obey the same rule.

A contract cannot own and view the same memory. Click refuses such a contract
when the function is entered and again when a call to it is planned, naming the
clauses that overlap. Reading through a second pointer needs no second clause:
ownership already authorizes the read, however the address is written.

Borrowing is partial. `owns a[0..8]` can supply a helper's `views a[2..4]`, and
the caller keeps `a[0..2]` and `a[4..8]` writable for the call; the lent middle
comes back at the return. Overlap is decided in bytes rather than in elements,
so an `int32` owner and a `uint8` view of the same storage conflict.

This matters at deallocation. `free` requires allocation authority and complete
owned access, then rejects any other direct or composite resource that may
still refer to the freed allocation. A live borrow of any part of an allocation
also blocks freeing or reallocating it, because the borrow protects the
allocation's lifetime and not only its bytes. A call's own borrow has ended by
the time the call returns, so it does not block a later `free`; a view proved
separate from the freed allocation survives. When several allocation
authorities are held, `free` selects the one whose evaluated base pointer
matches the argument; unrelated authorities remain available for later
deallocation.

## Owned memory

An owned memory resource permits both loads and stores. An owner reads its own
memory directly and never needs a view of it. Stores update the symbolic memory
state; later reads of the same cell see the written value unless a later write
changes it again.

<!-- verified-example: mdtests/resource_summary_splits_write_range.md -->
```click
int32 write_first(int32 p[]) {
    owns p[0..1];
    ensures writes_first: p[0] == 1;
}
```

Owned memory resources are linear across function calls. `owns` transfers the
resource to the callee and returns it; `consumes` transfers it without returning
it. The caller cannot use a consumed resource afterward.

This is the main difference between an owned resource fact and an ordinary
proposition. Ordinary facts can be used repeatedly. An owned resource can be
transferred.

## Function calls

Function calls use the callee's verified contract as an opaque summary:

<!-- verified-example: mdtests/permission_call_returns_write.md -->
```click
int32 write_and_return_permission(int32 p[]) {
    owns p[0..1];
    ...
}

int32 call_write_and_keep_permission(int32 p[]) {
    owns p[0..1];
}
```

The caller must have a resource that covers every callee resource requirement.
`step()` checks the pure and resource preconditions, advances across the
entire call, transfers the declared resources, applies the memory effect, and
adds the pure postconditions. It does not execute the callee body. The callee
must therefore have a contract in the sidecar, as a function the sidecar
verifies (in any order) or as an `extern` declaration; otherwise Click reports
that the sidecar states no contract for it. A viewed range rooted in a caller
local is borrowed from the caller frame's implicit ownership; external ranges
still require explicit resource facts.

Postconditions are the caller's only knowledge of changes made by an opaque
call. For example, a setter must state `ensures p[index] == value` if callers
need that fact. A true implementation detail that is absent from the contract
is deliberately unavailable. `old(...)` in a callee postcondition refers to
the state at that call's entry.

Public postconditions remain usable when a call result is assigned to a C
local and that local is passed to later verified calls. Click can compose the
result equality with those later calls' postconditions, including across
explicit `at(...)` points. Expansion writes the chain with source C
locals and fields; symbolic call identities, havoc markers, and other
execution-only facts remain kernel details rather than Surface Click premises.

When the C never assigns the result to a local — `if (f(x))` and
`return f(x);` — the call step's `let` binder names it instead, so the
postcondition and the branch or return fact can be related in one proposition.
See [naming a call result](proof-scripts.md#naming-a-call-result).

An opaque call first creates proof obligations for the callee's `requires`
clauses. Those requirements are then available as established assumptions while
Click evaluates the remaining resource, effect, and postcondition clauses of
that same contract. A requirement such as `1 <= n` can therefore justify a
later footprint rooted at `p + (n - 1)`.

A contract's clauses are read as one set, at the callee's entry and at every
call to it. A resource clause whose address loads a cell another clause holds,
`owns pair(node)` supplying the link that `owns pair(node->left->left)` loads,
is evaluated against what the whole set supplies, including the cells inside a
folded composite the set owns. At a call the same holds for a precondition that
reads such a cell and for the returned borrow: both are read through the
transferred clause set opened by its definitions, so the caller needs no
`observe` or `unfold` to make a dependent clause addressable. A read the
callee's own clauses cannot justify is refused at the callee's entry, before
any call.

A folded field-bearing instance supplies its sibling clauses the same way
when its body is unconditional and unmatched. `arena_prefix_region(region)`
carries the fields `start` and `end` and owns `*region`, so a contract
that consumes `freed: arena_prefix_region(region)` may also consume
`arena_prefix_state(region->arena)`: while the clauses are evaluated, the
instance's body is evaluated once at its own fields and the cells it owns are
published as views. Clause order does not matter, and the clauses a contract
returns are read the same way: `owns st: arena_prefix_state(region->arena)`
beside `owns r: arena_prefix_region(region)` returns `st` at the address `r`
supplies, and contract certification reads a postcondition's cells inside
the contract's folded instances, such as
`result == region->arena->data[region->start + index]`, through the cells
their bodies own. A field-free composite the body owns publishes its cells
the same way, so `arena_state` publishes the occupancy map its
`arena_cells` child owns and a postcondition may read `arena->occupied[k]`
before and after the call. A guarded
body publishes nothing, since its case is a proof obligation rather than a
premise; a matched body publishes the arm its premises decide, described
under [Modeled bodies and arm selection](#modeled-bodies-and-arm-selection);
and a body with existential witnesses publishes nothing. Only the section's
own clauses publish; the rest of the frame the section is evaluated against
is never opened for this purpose.

Named produced-resource arguments use this same read authority from the call's
own input instances, including the arms the entry premises already select.
For `produces root->node; produces leaf: cell(root->node);`, a matched input
bundle owning `root->node` supplies the index read just as an unmatched bundle
does. Current arguments read post-call memory; `old(...)` arguments retain
entry authority and memory. This temporary argument frame does not export a
view of a consumed field to the caller. Regressions are
`mdtests/produced_resource_index_reads_matched_input_field.md`,
`mdtests/produced_resource_index_uses_post_call_pointer.md`, and
`mdtests/produced_resource_index_does_not_export_input_views.md`.

The publication is read authority and nothing more. The instance stays folded,
so a store to a cell it owns is refused until an explicit `unfold` moves the
cell into the proof state, and a cell the body does not own is not published
at all. This publication belongs to the contract's own clauses at its entry
and return; it is not one of the frontiers where a matched instance's arms
are decided, so a loop head does not read through a folded field-bearing
instance. The regressions are
`mdtests/contract_returns_field_bearing_sibling.md` (both clause
orders), `mdtests/borrowed_instance_argument_reads_old_field.md` (a caller applying
such a contract),
`mdtests/arena_prefix_free_reads_region_arena.md`,
`mdtests/contract_field_bearing_instance_views_grant_no_write.md`, and
`mdtests/contract_field_bearing_instance_views_only_owned_cells.md`.

One checked resource transition serves every way a contract is applied: a
direct call, a call through a function pointer under a named contract, an
explicit execution theorem, and independent certification. The transition
records what the caller lends and consumes, what the caller keeps, the write
footprint the callee's clauses denote, and what the call returns. Where a
proof binds the callee's instance binders, by a call map or by a named
contract's proof arguments, one kernel check binds them: an instance the
caller does not own, or one instance supplying two binders, is refused the
same way in either form.

A held instance supplies a required one when their arguments are proved
equal. A pointer argument of a declared resource is compared by address and
provenance, not by the view a cast selects: the resource names the object at
the address, and the view only bounds C accesses through the pointer, which
the resource's own clauses check when they are evaluated. A kernel token whose
identity is itself bounds evidence keeps the complete comparison, so a member
pointer does not claim its enclosing object's `allocation(p, n)`
(`mdtests/a_member_pointer_does_not_claim_its_enclosing_allocation_bounds.md`). A caller holding `size_metadata(rb_old)`
therefore supplies a callee's `size_metadata(node as (uint8 *) as (struct rb_node *))`
for `node = container_of(rb_old, struct sized_node, rb)`
(`mdtests/a_resource_argument_matches_across_a_cast_that_selects_another_view.md`),
and an instance for another node still does not
(`mdtests/a_resource_argument_of_another_node_does_not_match.md`).

An unannotated callee receives no external memory permission, even if the
caller has permissions in its own context. The callee's owned resources provide
the precise abstract write footprint. Without one, an owned input resource is
used as a conservative write footprint.

Loads outside that footprint are preserved across the opaque call. This
includes adjacent struct fields and composes across several calls, so callers
do not need to save and restore unchanged metadata merely to give it a stable
name in the proof. Expansion exposes only ordinary source-level premises such as
the relevant `viewable(...)` range; call-havoc identities remain internal.
Preserving a dependent load such as `owner->data[i]` additionally requires the
address inputs (`owner->data` and `i`) and the target range to remain stable.
If any owned range may overlap the loaded field, Click does not transport the
equality.

Opaque summaries support comparison, logical, quantified, predicate-call,
`separate(...)`, `contains(...)`, and `viewable(...)` propositions, including
`old(...)` and `at(function.entry, ...)`. A contract containing an `at(...)` of
an internal statement or loop point can still be verified directly, but that
point is not visible at an opaque call site. Calling such a function reports
that its contract cannot be exposed opaquely rather than reporting a dependency
ordering error.

### Producing a view

A function can leave a bare memory view in its caller's resources:

<!-- verified-example: mdtests/explicit_produced_view.md -->
```click
int32* first(int32* left, int32* right) {
    views *left as left_input;
    views *right;
    produces view(*left) from left_input;
    ensures result == left;
}
```

`from left_input` selects the input view that must cover the output. The
produced view keeps that borrow active after the call. A write through any
pointer to the protected memory is blocked. Other disjoint memory remains
writable. The pure postcondition relates the resource to the C result.

When exactly one input view has the same lowered memory range as the
output, `produces view(*left);` selects it directly. The base expression,
bounds, and element width must match. An alias equality or a larger input
range can justify coverage once you name the source with `from`. An output
with zero or multiple direct matches requires that explicit source.

In a caller's proof, `release_view(*p);` gives up the exact held memory view
when `p` points to that cell. Other views sharing its hold remain usable.
The hold ends when its last view is gone. Once all holds end, the borrow can
restore the ownership the caller lent. A borrowed input of the caller still
has its own lifetime. Releasing the view is a proof step with no C operation.

## Abstract resources

You can declare an exact-match abstract resource:

<!-- verified-example: mdtests/token_resource_borrow_return.md -->
```click
abstract resource open_fd(fd: int32);
```

Then a contract can require and return instances of that resource:

<!-- verified-example: mdtests/token_resource_borrow_return.md -->
```click
int32 borrow_fd(int32 fd) {
    owns open_fd(fd);
}
```

An abstract resource is transferred by function calls. If a callee `owns
open_fd(fd)`, the caller gets the token back. If the callee `consumes
open_fd(fd)`, the caller loses the token.

Abstract resources currently have exact-match behavior only. They do not split,
rejoin, imply other resources, authorize C statements, or define custom algebra
rules. Resource arguments currently support current-state C expressions such as
parameters, constants, arithmetic, pointer expressions, and indexes. Arguments
are checked against the types declared in the resource definition. They have no
local `fold` or construction rule: a contract may assume, transfer, return, or
consume an abstract unit, but verified code cannot establish its first unit.

An abstract resource may also declare fields, `abstract resource obj(p:
int32*) { field size: int32; }`. Each instance is then named, as a declared
resource with fields is, and carries its fields, but the family still has no
body: no proof folds, unfolds, or observes an instance, so its fields are
exactly what the contracts that produce, pass, and consume it state
(`mdtests/abstract_resource_fields_pass_through_calls.md`).

Equal declared resources accumulate as an exact quantity. Duplicate clauses
such as two `consumes open_fd(fd);` entries require two units, and a call cannot
satisfy that requirement with one unit.

## Resource quantities

### Populations and authority

The [refcount example](https://github.com/clicklang/click/blob/master/examples/refcount/README.md) uses explicit
population authority. Its references and shared control are separate resources:

<!-- verified-example: mdtests/counted_resource_population_body.md -->
```click
authorized resource object_ref(obj: struct object*) {}
resource object_control(obj: struct object*) {
    owns obj->refs;
    owns authority(object_ref(obj));
    fact obj->refs == count(object_ref(obj));
}
```

Population accounting covers only families declared `authorized resource`.
`authority(...)` and `count(...)` may name only such a family; on any other
family they are refused. An ordinary family such as `object_control` folds,
unfolds and moves by its definition alone and creates or destroys no counted
member.

Observing a live population with `count(object_ref(obj))`
requires the matching authority.
An owned folded `object_control(obj)` also permits the observation: Click checks its
definition and current custody as if opening it for the count read and closing
it again. The observation grants no field access or permission to change the
population. A view, a control for another population, or a transferred
authority cannot justify it. At function entry the count is arbitrary,
constrained by the control invariant and supplied preconditions; it is not zero.
Contracts and proof expressions use the same checked rule.

Locally created concrete batches can be consumed in pieces: after
`fold(3 of token(p))`, `unfold(token(p))` leaves two members, and
`unfold(2 of token(p))` leaves none. Each change requires the matching authority;
zero quantities also require authority and leave the population unchanged.
Retirement still requires all members to have been consumed. The
[local numeric batch fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_local_numeric_batch.md)
checks this without enumerating the members.

A resource quantity may read memory supplied by another required resource in
that contract section. For example, `owns control(pool)` can supply the field
read in `owns pool->capacity of slot(pool)` when its body owns the pool's
memory, even while the control stays folded. Clause order does not matter.
This read exposes neither the authority nor mutable memory ownership;
changing the field still requires opening the control. Authority alone, or
zero copies of a control, does not supply its memory. The
[folded-quantity fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_control_quantity_read.md)
checks both orders. The quantity read itself does not transfer ownership.

Creating or consuming a reference requires exposed authority, and opening the
control exposes its owned counter field. Updating both the field and the
population by the same amount lets the proof restore the control invariant.
Authority must be consumed at count zero before its storage is freed. This
checked operation preserves the fact that the exact family is empty:
`count(object_ref(obj))` can still equal zero in a final postcondition after
`unfold(authority(object_ref(obj)))` and after `free(obj)`. It grants no
ownership, field access, or permission to create or consume members. Merely
knowing that a pointer was freed does not establish an unrelated family’s
count. The [cleanup fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_count_after_cleanup.md)
checks this observation before and after free.

An ordinary helper may borrow a folded control and an unchanged whole slot
batch with `owns control(pool); owns pool->capacity of slot(pool);`. The
helper must return both. Authority custody and batch custody move separately:
receiving only one grants neither the other's ownership nor permission to
consume members. A field-valued zero quantity moves no member rights. The
[zero-quantity helper fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_symbolic_batch_helper_zero.md)
checks a helper that borrows the control and its whole field-valued batch,
called from one that holds a zero batch. A cleanup helper can instead consume the
control and complete entry-sized batch with `consumes`, retire its authority,
and return ordinary storage with `produces *pool`. The
[symbolic cleanup helper fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_symbolic_batch_cleanup_helper.md)
checks direct, nested, and zero-sized calls. Call application consumes the
checked entry quantity even when the helper changes the accounting field.
Retired consumption evidence remains available to the certificate checker;
it grants no live authority or member rights. When the consumed control owns
several authorities, cleanup checks and retires each one. Additional
populations must have zero global count and no outstanding member custody;
local absence alone does not establish emptiness. The
[pool cleanup fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_pool_control_cleanup.md)
checks the original pool cleanup C at an arbitrary entry capacity, including
zero. A caller unfolds and refolds the control to establish the required
conservation and empty-population facts before calling cleanup. A caller
holding a concrete numerical batch can pass it to an entry field-valued
quantity when an available equality identifies that field with the sender's
complete held batch. The equality moves only those existing members;
it cannot substitute a global count for custody or permit consumption without
authority. The [field-quantity cleanup fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_pool_cleanup_field_quantity.md)
checks two owned slots passed as the cleanup helper's entry capacity.
A helper that creates a fresh symbolic quantity can return that exact whole
batch with `produces amount of slot(pool)`. The transfer changes batch custody
without changing the already-checked population delta or moving preexisting
members. It requires the actual born quantity and its current holder; returning
a different quantity or spending the transfer twice is rejected. The
bounded-pool example's [`pool_grow`](https://github.com/clicklang/click/blob/master/examples/bounded-pool/bounded_pool.click)
checks this boundary with arbitrary entry totals and nonnegative growth,
establishing the count addition's definedness from the control before the
birth, and the
[large symbolic birth fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_large_symbolic_population_total.md)
returns a helper's fresh symbolic batch through its caller. Splitting batches
remains separate work.

A unit-exchange helper can move one unit of each of two families between two
distinct anchors. It consumes the two incoming members and produces the two
outgoing members using ordinary `consumes` and `produces`; all four matching
authorities are borrowed and returned with `owns`. This covers moving an object
to another pool while consuming its destination slot and returning a source
slot. Every transition has separate authority, exact-identity, and custody
checks. The [four-effect fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_four_effect_exchange.md)
retains neighboring ownership and checks all four resulting counts. Omitting a
consumption reports `Requires consumes R(...)`; extra births are rejected even
without count postconditions. Click supports unit exchanges, not
arbitrary groups of symbolic effects.

For an authority passed into a function, retirement checks both that its
member custody has been consumed and that its authenticated global count is
zero. This applies to an already-empty population and to a fully consumed
numeric or symbolic batch. Consuming only the members owned by the function
is insufficient when the global population includes other members; writing
an accounting field to zero does not consume those members. The
[pool cleanup fixture](https://github.com/clicklang/click/blob/master/mdtests/authority_pool_control_cleanup.md)
consumes the entry-capacity slot batch, checks the private-object population
is empty, and retires both authorities while keeping the pool's C storage.

Ordinary wrappers can package existing members with `owns R(p)` and later
expose them with `unfold`; these transfers require no authority and do not
change the population. A wrapper cannot create a missing child or bypass the
authority requirement for membership changes. The source-backed
[transfer fixture](https://github.com/clicklang/click/blob/master/mdtests/counted_resource_transfer.md)
checks packaging after a C return as well as ordinary helper transfer.

A release helper can consume control and a reference, then conditionally
produce the control on its nonfinal branch using the existing guarded
`produces` clause. The final branch consumes its last reference, retires
authority, and frees storage. Numeric nested calls transfer these capabilities
explicitly; a helper cannot strand a reference while returning control.
The [branch-on-count release fixture](https://github.com/clicklang/click/blob/master/mdtests/child_release_branch_on_count.md)
checks both lifetime branches and the exact count decrement.

An authority-bearing resource need not tie its count to a C field. Before an
initializer writes the C counter, its storage resource can carry authority
with an arbitrary logical entry count; `requires count(R(p)) == 0` establishes
the initializer’s empty-population precondition. Click does not assume zero
or read an uninitialized field to obtain that count. The
[initialization fixture](https://github.com/clicklang/click/blob/master/mdtests/population_initialized_cleanup.md)
checks that the initializer still produces its first reference.
Standalone symbolic batch exchange and whole-batch helper custody are supported.
Composing additional population changes with an already-updated symbolic batch
remains separate work.

For a field-free family with several arguments, one authority can govern all
members sharing a concrete storage anchor:

<!-- verified-example: mdtests/authority_wildcard_lifecycle.md -->
```click
authorized resource slot(pool: int32*, member: int32*) {}
```

`fold(authority(slot(&pool, _)))` establishes the empty population in the
environment that created `pool`. Folding `slot(&pool, &first)` or
`slot(&pool, &second)` requires that authority and increases
`count(slot(&pool, _))`. Unfolding requires the particular owned member and
the authority, and decreases the total. Retirement requires zero members.
Another pool has a separate authority. With more arguments, every argument
after the anchor is a wildcard, as in `authority(slot(pool, _, _))`.

An ordinary helper can borrow and return wildcard authority together with one
concrete member:

<!-- verified-example: mdtests/authority_wildcard_helper_borrow.md -->
```click
void inspect(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    owns slot(pool, member);
    ensures count(slot(pool, _)) == old(count(slot(pool, _)));
}
```

The helper's entry total is arbitrary, including members owned elsewhere.
Receiving one member gives a lower bound of one, not an exact total of one.
The call returns the same authority and the same concrete member, preserving
the caller's total and any members it retained. Nested helper calls use the
same checked transfer. The helper receives no population creation permission.

A member can own a private memory body independently of population authority:

<!-- verified-example: mdtests/authority_wildcard_private_body_helper.md -->
```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
int32 update(int32* pool, int32* p) {
    owns slot(pool, p);
    ensures result == 7;
    ensures p[0] == 7;
}
```

`with(slot(pool, p)) { ... }` exposes that member's memory and requires the
same body to be restored on close. Neither step changes membership. The
helper needs the member, while its caller can retain authority and other
members. Two members can own disjoint cells of the same allocation, and
nested opens keep their ownership separate. Owning one member grants no
access to another member's cells and no population count observation.
Creating or consuming a member still requires authority and transfers its
private memory into or out of the member. Merely having a scalar local does
not supply separable memory ownership to package into a member.
Click covers owned memory ranges without member facts or proof fields.

An authority-only helper input can also create one field-free member:

<!-- verified-example: mdtests/authority_wildcard_create_helper.md -->
```click
void issue(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, member);
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) + 1;
}
```

The proof folds the promised member. This is a checked population birth, not
authority establishment: entry supplies an existing population with an arbitrary
total, which may include members held elsewhere. The count bound is required
before the birth. The returned member keeps its concrete arguments, and the
caller recovers authority with its total increased by one. Nested creation
helpers use the same transfer. This initial creation support admits one birth
from an input containing authority and any required private memory; it does
not replace a borrowed member or consume another population member.

A memory-bearing member is created by transferring its private memory into
the helper:

<!-- verified-example: mdtests/authority_wildcard_create_private_body.md -->
```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes p[0..1];
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, p);
    ensures p[0] == 7;
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) + 1;
}
```

The C body can update the supplied memory before `fold(slot(pool, p))`
packages it into the new member. The caller recovers authority and that
member, including through nested helpers, while retaining its other members.
The helper cannot return independent ownership of the packaged memory as
well, and authority cannot supply missing memory. The overflow bound remains
required for the arbitrary entry total. This uses ordinary `consumes` and
`produces`; no additional resource operation is needed.

The corresponding consumption helper borrows authority and takes one member:

<!-- verified-example: mdtests/authority_wildcard_consume_helper.md -->
```click
void release(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    consumes slot(pool, member);
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
}
```

Its proof uses `unfold(slot(pool, member))` to consume that exact member, or
delegates consumption to a checked nested helper. Holding the input member
establishes that the arbitrary entry total is at least one, so decrementing
needs no additional bound. Return checks the member's checked consumption;
merely declaring `consumes` and returning authority does not suffice. The
caller retains its other members, recovers authority, and observes the total
decreased by one. The consumed member cannot be used again. This single-pool
form admits one consumption of the entry member. The two-pool move below
also produces a member under a different authority.

A consumed member can return its private memory through the ordinary output
contract:

<!-- verified-example: mdtests/authority_wildcard_consume_private_body.md -->
```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
void release(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes slot(pool, p);
    produces p[0..1];
    ensures p[0] == 0;
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
}
```

Here `unfold(slot(pool, p))` consumes the member and exposes its memory for
the C body to update. `produces p[0..1]` returns that memory to the caller;
it does not recreate membership. The caller retains its other member and
recovers authority with the decremented count, including through nested
helpers. It can use the returned memory and reclaim the allocation once all
its remaining memory ownership is available. It cannot reopen the consumed
member or read the memory after freeing it. Opening and closing the member
without consuming it cannot satisfy this contract.

A private member body can also carry ordinary invariant facts:

<!-- verified-example: mdtests/authority_wildcard_body_facts.md -->
```click
authorized resource slot(pool: int32*, p: int32*) {
    owns p[0..1];
    fact 0 <= p[0];
}
```

Folding must establish the fact at the current memory state. Opening exposes
it, and closing must restore it after any C writes; the fact at an earlier point
cannot justify closing after an invalidating write. Consuming the exact
member exposes its memory and invariant together. A helper may open and close
the member without holding population authority, preserving membership.

These facts may depend on the member's arguments and its privately owned
memory. Ambient ownership of another cell does not let the member promise a
fact about that cell. Click supports unit members with field-free,
owned-memory bodies, not named proof fields, aggregate count invariants inside
members, or independent external lifetime claims. Population-wide facts belong
in the authority control resource.

A population member may instead own another ordinary declared resource:

<!-- verified-example: mdtests/authority_wildcard_contained_resource.md -->
```click
resource cell(pool: int32*, p: int32*) { owns p[0..1]; }
authorized resource slot(pool: int32*, p: int32*) { owns cell(pool, p); }
```

Folding `slot(pool, p)` transfers the already-owned `cell(pool, p)` into its
body and increments the slot population. Consuming the slot returns that exact
cell and decrements the slot population. These operations preserve the cell's
membership in its own population, if it has one; they do not create or destroy
that cell. Ordinary helpers express these transfers with `consumes` and
`produces`, including nested calls. Their count changes concern the outer
member only.

`with(slot(pool, p))` temporarily exposes the cell. Inside that block,
`with(cell(pool, p))` exposes its memory for C access. Both scopes must restore
their owned contents, and neither requires population authority. Missing or
mismatched children cannot establish the outer member; its child cannot also
be returned as independent ownership while retained inside the folded member.
Built-in `owns *p` also works inside a member body. Click
supports unit owned contents in field-free bodies; named proof fields,
conditional contents, and counted batches with nonempty bodies remain separate.
Private facts inside each resource layer follow that layer's existing checks.

A helper can move a unit member between two authorities of the same family:

<!-- verified-example: mdtests/authority_wildcard_transfer_private_body.md -->
```click
void move(int32* source, int32* destination, int32* p) {
    requires source != destination;
    owns authority(slot(source, _));
    owns authority(slot(destination, _));
    consumes slot(source, p);
    requires defined(count(slot(destination, _)) + 1);
    produces slot(destination, p);
    ensures p[0] == old(p[0]);
    ensures count(slot(source, _)) == old(count(slot(source, _))) - 1;
    ensures count(slot(destination, _)) == old(count(slot(destination, _))) + 1;
}
```

Its proof unfolds the source member, then folds the destination member using
that same private memory, or calls a checked nested helper. Both authorities
are borrowed and returned. The destination entry total is arbitrary; owning
its authority gives no ownership of its existing members. Each population's
ledger checks its own exchange, while ordinary resource transfer checks the
private body. Caller-retained members in both pools remain owned. The old
source membership cannot be reused. This transfer admits one unit consumption
and one unit production with the same family and trailing arguments, changing
only the pool anchor; it does not enable arbitrary batches of updates.

A helper can also exchange one member between two different families at the
same anchor. This is the checkout pattern: consume an available capacity unit,
then package supplied object ownership into a checked-out member.

<!-- verified-example: mdtests/authority_family_exchange.md -->
```click
void checkout(int32* pool, struct payload* p) {
    owns authority(capacity(pool));
    owns authority(item(pool, _));
    consumes capacity(pool);
    consumes *p;
    requires defined(count(item(pool, _)) + 1);
    produces item(pool, p);
    ensures p->value == old(p->value);
    ensures count(capacity(pool)) == old(count(capacity(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
}
```

Both authorities are borrowed and returned. A direct unary authority exposes
an arbitrary entry count, just like a wildcard authority: the one capacity
unit supplied to this helper proves a lower bound, not the entire total.
The proof consumes that unit and creates the item through the ordinary
`unfold` and `fold` operations. Each family's ledger checks its own change;
ordinary resource ownership separately checks the item's private body.
Nested helpers follow the same rule, and caller-retained members stay owned.
This initial exchange supports one unit consumption and one unit production
under explicitly borrowed authorities, with different families at the same
anchor. It does not admit arbitrary batches or authority replacement.

Private external memory can use its checked `viewable(...)` facts together with
owned body resources. A modular helper must separately export any
payload-value guarantee the caller needs.

An ordinary control resource can own both authorities and the C fields that
record their totals. A checkout helper borrows that control as one resource:

<!-- verified-example: mdtests/authority_pool_control_two_members.md -->
```click
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
    fact pool->capacity == pool->checked_out + count(slot(pool));
}
```

The helper contract uses `owns control(pool)`, `consumes slot(pool)`,
`consumes *p`, and `produces item(pool, p)`. Its proof opens the control,
consumes the slot, increments the C counter, creates the item, and closes the
control. Closing checks both relationships against the updated ledgers;
retaining the authority alone cannot restore a false invariant. Nested helpers
transfer the same control, and callers can retain additional slots
(`mdtests/authority_pool_control_two_members.md` calls `checkout` while its
caller keeps the second slot).

The fixture requires `pool->checked_out < 2147483647` to establish that the C
increment is defined. It uses the existing unit-transfer sum theorem to restore
the capacity equation. Certificate checking verifies that the original sum,
increment, and predecessor are all defined before cancelling the two unit
changes; wrapping arithmetic cannot justify the new sum's domain.

Click supports one or two distinct authority scopes at the same
pointer anchor in a field-free control with owned memory and at most one
allocation. Every contained authority is authenticated and transferred
separately. An imported control assumes an existing population, never an empty
one or a new creation right. General control bodies and more than two
authorities remain separate work.

A wildcard authority also permits an exact member count. `count(slot(pool, p))`
counts every existing unit with those arguments; `count(slot(pool, _))` counts
the whole family. Equal empty members can have a count greater than one. Owning
one member establishes a lower bound, not equality to one.

<!-- verified-example: mdtests/authority_wildcard_exact_count.md -->
```click
void release(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    requires count(slot(pool, p)) == 1;
    consumes slot(pool, p);
    produces p[0..1];
    ensures p[0] == 0;
    ensures count(slot(pool, p)) == 0;
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
}
```

The helper's exact entry count is arbitrary unless its contract constrains it.
Consuming the member subtracts one from that exact count as well as the total.

An exact member's count is its own term, even where the facts prove the
population empty. The kernel law `population_member_count_zero` relates the
two: `apply(population_member_count_zero(count(slot(pool, p))))` needs the
available fact `count(slot(pool, _)) == 0` and adds
`count(slot(pool, p)) == 0`. Both counts are the ones `count(...)` lowers to
at the current state
(`mdtests/an_empty_population_counts_no_member.md`,
`mdtests/an_empty_population_law_needs_the_population_count.md`).
Creation similarly adds one; a helper promising an exact result of one can
require an exact entry count of zero. Other concrete members keep their counts.
Neither observation gives permission to open their private bodies.

This initial exact-count support covers concrete pointer/`int32` indices and a
helper's selected concrete member. It rejects unresolved indices rather than
reporting an unproved zero, and does not yet observe another potentially aliased
member inside that helper. Partially fixed wildcard patterns and exact counts
in symbolic batches remain separate work.

This scope support covers field-free members, aggregate wildcard observations,
and helper contracts that borrow and return one concrete member with their
authority, consume the entry member, or create one from authority and its required
private memory, move one unit member between two wildcard authorities, or exchange
one unit between two different families at one anchor. Fixed
trailing arguments in authority patterns, partially fixed subset observations,
and field-bearing members remain future work.

### Quantities

Equal owned units of a declared token are stored as one canonical fact with a
quantity:

<!-- verified-example: mdtests/authorized_abstract_token_quantity_borrow.md -->
```click
authorized abstract resource object_ref(object: struct object*);
```

A clause without a coefficient transfers one unit: consuming one
`object_ref(object)` from a quantity of two leaves one unit behind. An owned
user-declared resource may use `owns amount of object_ref(object)`,
`consumes amount of ...`, or `produces amount of ...` to transfer a runtime
`int32` quantity algebraically. The coefficient must be proved nonnegative at
the contract's point, and zero grants no authority. It grants no body facts
either: a composite's body facts describe each instance a quantity counts, so
they are available only where the quantity is known to be positive
([`owning_zero_of_a_composite_grants_no_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/owning_zero_of_a_composite_grants_no_body_fact.md)).
Viewed facts remain idempotent and do not carry a count.

Symbolic coefficients are rejected for memory, allocation, and recursively
defined composite resources. Those families need distinct semantics; Click
does not interpret a symbolic coefficient by expanding it into repeated facts.

`count(object_ref(object))` observes the exact quantity of an `authorized`
family under its owned authority. Two keys of one family name one population
whenever their arguments are equal, so a count or a transfer of `object_ref(p)`
beside a tracked `object_ref(q)` needs `p == q` or `p != q` established; with
neither, the count has no value the facts determine and `click verify` refuses
the observation or the transfer rather than totalling the entries it happens to
have proved equal. Declaring a resource does not by itself justify minting a
unit: members are created and destroyed only under the authority, and the
control that owns it keeps its facts true across each change.

A worker thread receives members and the authority through ordinary checked
transfers; the [worker authority protocol](../internals/worker-authority-protocol.md)
describes how a created worker borrows the authority and what its join
returns.

Inside `count(...)`, `_` is a wildcard over one resource argument. For example,
`count(pool_object(pool, _))` sums all exact object populations for `pool`.

A count is a nonnegative number that fits in an `int32`, and Click holds
contracts to that. Wherever two quantities for one population are added — two
clauses of one contract, two facts in one state, two entries under one
wildcard — the total has to be one Click can state exactly, or the two
quantities stay separate and the contract that needs them added is refused.
Separate populations do not imply that their sum fits; a wildcard observation
must establish that condition where it is used.
Constant quantities are added when their sum fits, and a quantity split off a
population recombines with its own remainder. Without that rule, `produces
2000000000 of tok(o)` twice composed to a population of `-294967296`, and
`ensures count(tok(o)) < 0` was provable of a function that had just produced
four billion units.

A function spec may exist only to consume a resource:

<!-- verified-example: mdtests/callback_resource_complete_once.md -->
```click
abstract resource can_complete(cb: int32);

int32 complete(int32 cb) {
    consumes can_complete(cb);
}
```

That spec contributes a call summary. Calling `complete(cb)` consumes
`can_complete(cb)`, so a second call on the same path fails unless some other
contract returns the resource.

## Composite resources

Declarations with a body define composite resources. The body is a one-layer
definition: it names contained resource facts and pure facts that justify the
abstract resource fact.

<!-- verified-example: mdtests/composite_resource_observe_nested_fact.md -->
```click
resource nonnegative_fd(fd: int32) {
    fact fd >= 0;
}

resource live_fd(fd: int32) {
    owns nonnegative_fd(fd);
}
```

A function that holds `live_fd(fd)` owns the folded abstract resource. It does
not automatically get every nested fact. `observe(resource)` takes one
non-consuming view step:

<!-- verified-example: mdtests/composite_resource_observe_nested_fact.md -->
```click
int32 return_fd(int32 fd) {
    owns live_fd(fd);

    ensures result >= 0 by {
        observe(live_fd(fd));
        observe(nonnegative_fd(fd));
    }
}
```

The first `observe` exposes a viewed `nonnegative_fd(fd)` resource. The second
`observe` exposes that resource's immediate fact, `fd >= 0`. Neither step
consumes `live_fd(fd)`, and neither step unfolds owned contained resources. This
one-step behavior is intentional: large composite resources should not be
recursively expanded by default proof automation.

The viewed fact an `observe` publishes from a resource the same context owns is
an observation, not a borrow. It is read authority derived from that owner and
is usable only while the owner is held; it cannot satisfy another function's
`views` clause, which only the checked lending transition supplies. When the
observed resource is itself borrowed, the published fact carries that borrow's
identity, so it stays tied to the borrow it was read through.

A guarded directly recursive resource also has a finite inductive witness.
`decreases list(node)`, or `decreases n;` naming the binder of an
`owns n: list(node);` clause, can use a direct contained child as a hidden
structural rank for a directly recursive C traversal. This does not turn
pointers into sizes and does not automatically unfold the resource: the proof
still uses `observe` or `unfold` to expose the layer it needs, while the
termination checker independently rechecks the declared child against the
exact resource definition. The recursive call path must establish the resource
guard (for example, `node != 0` or the equivalent nonnull arm of
`if (!node)`), either from an entry requirement or from C control flow. The
ordinary contract proof checks resource transfer,
so the traversal may consume and deallocate nodes after descending.

A child named through a `let` witness has no C name, so the checker
cannot compare it with the call's argument syntactically. It instead
instantiates the exact definition over a symbolic entry state: the guard and
the witness's `where` facts are assumed, the call's argument is evaluated in
that state, and the pure kernel must decide that the argument is the witness
pointer. In the marked list, `(node->word & ~1) as (struct node *)` is the
witness because the `where` fact and the alignment evidence determine it.
Loads on the call path are the same uninterpreted reads the syntactic
comparison relies on; the ordinary contract proof remains responsible for
the actual resource the call receives.

When code needs the contained owned resources, use `unfold(resource)`. When
the proof has rebuilt the body, use `fold(resource)`:

<!-- verified-example: mdtests/composite_resource_once_flag.md -->
```click
resource uncalled(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 0;
}

resource called(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 1;
}

int32 complete_once(int32 flag[]) {
    consumes uncalled(flag);

    produces called(flag) by {
        unfold(uncalled(flag));
        step_until(function.exit);
        fold(called(flag));
    }

    ensures result == 1 by {
        unfold(uncalled(flag));
        step_until(function.exit);
        fold(called(flag));
    }
}
```

`unfold(uncalled(flag))` consumes the folded `uncalled(flag)` resource and adds
the contained owned memory resource for `flag[0..1]` to the proof state. The C
execution can then mutate the flag. `step_until(function.exit)` runs it to the
function exit, which establishes the `called` body's exact fact;
`fold(called(flag))` checks it, consumes the contained owned resource, and adds
the folded `called(flag)` resource. If a body fact needs derivation, state it
first with `have ... by { ... }`; `fold` itself does not invoke `close()`. The
implicit tail at the end of the `by { ... }` block closes the overall claim.

`fold` also builds a composite resource from lower-level resources at a
function boundary:

<!-- verified-example: mdtests/composite_resource_once_flag.md -->
```click
int32 init_once(int32 flag[]) {
    consumes flag[0..1];

    produces uncalled(flag) by {
        step_until(function.exit);
        fold(uncalled(flag));
    }
}
```

Together, the three resource tactics are deliberately local:

- `observe(resource);` exposes one immediate view layer and consumes nothing.
- `unfold(resource);` consumes one owned composite resource and exposes its
  immediate body.
- `fold(resource);` checks exact declared body facts, consumes one immediate
  body, and produces the owned composite resource.

These steps are bounded by design. A proof that needs facts inside a nested
composite resource should name the path with repeated `observe(...)` steps
instead of relying on proof search through every possible nested body.

A function that returns a composite (`produces` it, or keeps it under `owns`)
may reach its exit holding the body's pieces instead of the folded head, and
a loop that keeps one may reach its back edge that way. Reading the pieces as
the composite there is a fold: the kernel accepts it only where every body
fact holds over those pieces, by the same exact check `fold` makes, and
otherwise reports the composite missing. A C store that falsifies a body fact
therefore needs the proof to restore the fact and fold, or the contract to
return something weaker
(`mdtests/an_ordinary_exit_does_not_produce_a_composite_whose_body_fact_a_store_falsified.md`,
`mdtests/a_loop_back_edge_does_not_return_a_composite_whose_body_fact_a_store_falsified.md`,
`mdtests/an_ordinary_exit_produces_a_composite_whose_body_facts_hold.md`).

### Borrowing a composite

`views` of a composite covers its checked one-level frontier. Lending one puts
the folded head in escrow and protects the direct memory children the
definition names; a contained composite becomes a read-only description under
the same borrow. Reading further down is projection: `unfold`, `observe`, and
`with` of a borrowed composite add the child to the borrow's permitted
descriptions after the kernel rechecks that the definition contains it. A
projection exposes nothing owned, so the depth a proof reaches costs nothing in
authority.

A fact in a lent body is stable for the whole borrow, because recovery restores
the exact head that was escrowed rather than refolding it. Two body shapes
cannot promise that and are refused when lent: a body whose facts read a
population count, which another call may change, and a definition whose facts
claim that storage the body does not own is still live.

A contract cannot lend a composite and own a piece of it at the same time. An
`owns` clause naming a cell inside a composite the same contract views is
refused as a proven overlap. Write a narrow effect as ownership of the whole
composite plus an `ensures` about the cells the function leaves alone.

A composite whose definition body contains a `views` clause is a struct holding
a borrow, such as a cursor over input it reads. A contract can name the input
that backs the cursor. For example, the initializer in
`examples/input-cursor/input_cursor.click` uses `views readable_input(data,
length) as input;` and `produces input_cursor(owner) from input;`. Each
viewed piece in the cursor must be covered by `input`. The source must have
backing that the caller can recover directly when the borrow ends.

Each produced cursor keeps its own hold on the input. Unfolding moves the hold
to its viewed pieces. Refolding all the pieces moves that hold to the new
head. Refolding a subset gives the new head a separate hold and leaves the
remaining pieces available. Consuming one cursor leaves the other holds live.
Once the last hold is gone, the caller can recover its original ownership.
A call that repackages an existing borrow can name a consumed composite with
`consumes cursor(...) as input` and write `produces other_cursor(...) from input`.
An `owns` clause carries the original resource and its borrow through the call.

On a failed return, the borrow diagnostic can name the output, the selected
input view, and the viewed piece it does not cover. A blocked write can name
the resource keeping the view live. When the caller directly holds a produced
memory view, `release_view` gives it up after its last use.

Members of an `authorized` family are the exception: they carry no body, so
folding one places no hold, and lending one member of a quantity leaves the
remaining members usable.

An ordinary exclusive resource needs no mutex-specific declaration to be
protected by a mutex. Initialization associates it: the proof supplies a
folded instance as the initialization's `state`, the mutex escrows it, locking
transfers it to the current execution path, and unlocking requires it folded
again. A helper names the association with a typed use, which identifies both
the mutex and the protected resource:

<!-- verified-example: mdtests/mutex_use_resource_type_without_annotation.md -->
```click
void increment(struct counter *counter) {
    owns access: mutex_use(&counter->mu, counter_state(counter));
```

In an execution proof, `held(&object->mutex)` states whether that path owns the
lock guard; it does not by itself grant the protected resource.

The built-in `mutex_guard(mu)` names the exclusive authority for the current
acquisition of `mu`. It grants no memory access by itself. A declared resource
can contain that authority using ordinary ownership syntax:

<!-- verified-example: mdtests/mutex_guard_resource_body.md -->
```click
resource holding(counter: struct counter*) {
    field tag: int32;
    owns mutex_guard(&counter->mu);
}
```

Folding consumes the existing guard; unfolding returns it. Unlock therefore
requires unfolding this wrapper first, as well as restoring any protected
assertion. A conditional resource arm may own the guard while another arm
owns none. The acquisition identity stays internal: `held(mu)` alone cannot
create a guard, and neither `views mutex_guard(mu)` nor a quantity is allowed.
A wrapper containing a guard is thread-confined, including through nested
wrappers.

A helper may preserve a folded guard-bearing instance with an ordinary
`owns h: holding(counter);` clause. The kernel frames its mutex protocol:
initialization, acquisition, release, and destruction are all forbidden while
checking that helper, and nested calls must satisfy the same preserving
boundary. The caller recovers the wrapper and the unchanged acquisition.

A helper can unfold and refold that wrapper, or receive the guard directly:

<!-- verified-example: mdtests/mutex_guard_direct_contract.md -->
```click
int32 read_locked(struct counter *counter) {
    owns mutex_guard(&counter->mu);
    owns state: counter_state(counter);
    ensures result == state.value;
}
```

The direct clause preserves the entry acquisition, including when the C body
reassigns its pointer parameter. The guard establishes `held(mu)`; the separate
`counter_state` supplies memory authority. A caller with a folded guard wrapper
must unfold it before passing the direct guard, and may refold it after return.
Missing guard inputs are reported as `Requires owns mutex_guard(...)`.

Named primitive binders such as `owns g: mutex_guard(mu)`, consuming or producing
guards, and lock-changing helper contracts remain unsupported. Calls without a
preserving mutex-authority input remain refused while a mutex protocol is live. An opaque
entry protocol without exposed guard authority does not establish `not held(mu)`.
Loop restrictions remain.

The separate `mutex_live(mu)` resource owns one initialization. Initialization
creates it, destruction consumes it, and lock currently requires it. It can be
packaged just like a guard:

<!-- verified-example: mdtests/mutex_live_wrapper.md -->
```click
resource lifetime(holder: struct holder*) {
    field tag: int32;
    owns mutex_live(&holder->mu);
}
```

Folded lifecycle ownership must be unfolded before lock or destroy. A direct
`owns mutex_live(mu)` contract preserves the entry initialization. The resource
implies neither `held(mu)` nor payload access and cannot be viewed or counted.
Borrowed `mutex_use` permissions, lifecycle-changing contracts, initialization
storage validity, and protection against ordinary writes are not implemented
yet. Automatic objects containing initialized mutexes must have them destroyed
before scope exit, including abrupt exits; folded authority does not bypass
this check. See the
[`mutex_live` primitive](../reference/language/index.md#mutex_live) for this boundary.

A contract clause speaks about parameters, so `consumes t: tree_at(root);`
names the tree at the entry argument. These tactics are not contract clauses:
they name the state the execution has reached. After `root = root->left` a
`fold(ctx_at(root), ...)` is the frame of the node the proof is standing on,
and a body fact such as `fact parent->left == child` instantiates to the link
the body just walked. The fold's field values are read the same way, so one
tactic never straddles two states
(`mdtests/fold_argument_reads_current_cursor.md`). An explicit `old(...)`
argument selects function entry even in a fold with explicit fields: after
`p = q`, `fold(saved_at(old(p)), { model: old(saved.model) })` keeps the
entry-indexed instance, while `fold(saved_at(p), ...)` selects the current
pointer. The argument and field initializer retain their own `old(...)` or `at(...)` points
(`mdtests/fielded_resource_fold_keeps_entry_arguments.md`); a current-pointer
model cannot establish the old instance's body
(`mdtests/fielded_resource_fold_rejects_current_model_for_entry_argument.md`).
A resource argument may also read an owned field through a proved model-pointer
alias. Named folds retain the facts already checked at that point when
evaluating those arguments; a model pointer without read authority is refused
(`mdtests/fold_argument_reads_through_model_pointer.md` and
`mdtests/fold_argument_model_pointer_needs_read_authority.md`).

### Conditional and recursive bodies

A composite resource may put its entire body under one load-free `if`:

<!-- verified-example: mdtests/recursive_conditional_resource.md -->
```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        owns list(node->next);
    }
}
```

The false case is an empty body; conditional resource bodies have no `else`.
The condition must not read memory. This avoids circular reasoning in which a
load is used to decide whether the memory resource authorizing that load
exists.

A guarded body may contain itself directly. `unfold(list(node))` exposes one
nonnull node and the still-folded `list(node->next)` tail; `fold` performs the
reverse step. Unknown guards remain opaque during automatic projection. Explicit
`observe`, `fold`, and `unfold` report that the guard must first be proved
true or false. Unguarded self-recursion and mutual
resource cycles remain rejected.

Declared resource identity respects proved equality of its arguments. This is
important after reading a next pointer: if the context proves
`node->next == tail`, ownership of `list(node->next)` is ownership of
`list(tail)` as well.

### Iterated guarded ownership

A body can own one element per index of a bounded range, selected by a
guard cell it owns. This is how an arena's occupancy map describes its free
cells: the arena owns `occupied`, and owns `data[k]` exactly while
`occupied[k] == 0`.

<!-- verified-example: mdtests/iterated_ownership_declaration.md -->
```click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}
```

The clause is a single resource fact, not `capacity` facts. The invariant it
keeps is simple to state: at every fold, the fact holds exactly the elements
whose guard is true in the current memory. Everything else follows from
keeping that invariant with local steps.

- `unfold(arena_cells(data, occupied, capacity)[j])` moves element `j` out while its guard is known true;
  the fact then makes no claim about `j`, and the element is ordinary owned
  memory that C can write.
- A C store to a guard cell is allowed only where the fact claims nothing:
  at an index taken out, whose guard is known false, or whose element the
  context owns outright. Marking a taken-out cell occupied (`occupied[j] =
  1`) closes the gap, because the guard is now false and the fact owes
  nothing for `j`. Clearing a cell whose element the caller owns
  (`occupied[j] = 0`) opens one, which `fold(arena_cells(data, occupied, capacity)[j])` closes by moving
  the element back.
- Whole-clause `fold` and `unfold` convert between the fact and the range its elements
  cover when a quantified fact decides every guard, which is what an
  initializer that zeroes the map needs.

No step visits the range. An indexed `unfold` reads one guard cell; a loop that claims a
run of `M` cells does `M` such steps; folding and unfolding the declaring
resource move one fact. Because the free cells are simply the cells whose
flag is clear, freeing two regions and reusing them for a larger run needs no
merge step
(`mdtests/iterated_ownership_released_cells_feed_an_external_claim.md`). The
language reference lists the declaration rules and the exact step conditions
under [Iterated guarded
ownership](../reference/language/index.md#iterated-guarded-ownership).

### Fields that choose cells

A resource's fields are its model: a folded instance holds their values, fold
proposes new ones, and unfold publishes the ones it held. Because that value
does not move while the instance is folded, a C-typed field may choose which
cells the body owns, exactly as a C expression over the parameters would:

<!-- verified-example: mdtests/resource_field_memory_endpoint.md -->
```click
resource zero_suffix(data: int32*, capacity: int32) {
    field start: int32;
    owns data[start..capacity];
    fact 0 <= start;
    fact start <= capacity;
    fact forall (k: int32) {
        start <= k and k < capacity implies data[k] == 0
    };
}
```

Unfolding an instance whose `start` is `s` owns `data[s..capacity]`; folding
with `{ start: s + 1 }` asks for `data[s + 1..capacity]` and checks the facts at
`s + 1`. No algebraic model or `match` is needed for a value that is just a
number; keep those for models with genuinely different shapes.

`unfold` gives the instance up, so after it the field has no instance to be
read from. The unfold pattern keeps the value by name, as a `match` arm keeps a
payload: `let { start: s } = unfold(before);` binds `s` to the value the
folded instance held. That name is ordinary proof data for the rest of the
function, which matters most in a loop: a loop invariant reads `old(...)` at
the loop's entry, where `before` is already consumed, so the invariant has to
say `s`. Unfolding also names the cells such a body owns at their folded
values, as it does for a matched instance's selected arm, so a C read of
`b->p` after the unfold is the load the owned range `b->p[0..b->n]` was
written over. One pattern may name child slots and fields together; see
`mdtests/resource_unfold_binds_scalar_field.md` and
`mdtests/resource_unfold_binds_children_and_fields.md`.

A named owned child's C arguments may also be pure function calls, such as
`owns left: metadata_at(identity(left_model));`. The call uses the ordinary
typed pure-expression evaluator, so a logical model can supply a C pointer or
scalar index without reading the program's links. Its result must match the
child's declared C parameter type. Opening and rebuilding the resource use
the same checked expression; any read or safety conditions must already be
proved. Computing an address grants no additional memory authority.
`mdtests/resource_child_pure_arguments.md` exercises a model-derived address
through both `unfold` and `fold`. A C-valued field named by an unfold output
remains an ordinary value when passed as a resource argument; see
`mdtests/resource_unfold_field_used_as_argument.md`.

### Modeled bodies and arm selection

A body may instead branch on one algebraic field, so which cells the resource
owns depends on its model:

<!-- verified-example: mdtests/resource_match_arm_selected_at_contract.md -->
```click
resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}
```

An `if` guard is decided from the section's assumptions, and a matched field is
decided the same way. When a contract's requirements together with constructor
exhaustiveness leave exactly one arm possible, lowering exposes that arm's
cells as read authority, so `requires p->value >= 0` or `owns p->value->tag`
can address memory the folded resource owns. `c.model != Maybe::None` on a
two-constructor model selects `Some`, and so does
`exists (v: int32) { c.model == Maybe::Some(v) }`.

Selection is entailment, not search. A disequality against a constructor with
fields rules out nothing, and requirements that leave two arms possible select
neither. Click does not split the contract into cases to find out which arm the
caller meant. Selection also grants nothing but reading: ownership of the arm's
cells, and its contained child resources, still come only from an explicit
`unfold`. A loop head selects an arm the same way, with its invariants playing
the part the requirements play in a contract; the frontiers that decide an arm
are listed under [Where a matched instance's arms are
decided](#where-a-matched-instances-arms-are-decided) below.

Requirements that select no arm may still have refuted some, and the arms they
leave can agree about a cell. What every possible arm owns is then published,
as the same read authority a selected arm publishes: on a three-constructor
frame, `requires c.model != Context::Top` decides nothing, but the `Left` and
`Right` arms it leaves both own `parent->rb_right`, so that cell is readable
however the model turns out. What is published is the intersection of those
arms' own memory clauses, evaluated once per arm. A cell one possible arm does
not own is never published: the read is refused, and the diagnostic names the
instance and the arms the requirements left possible rather than leaving an
unexplained missing viewability. The positive is
`mdtests/resource_match_common_arm_cells.md` and the refusal is
`mdtests/resource_match_arm_needs_one_entailed_arm.md`.

A selected arm supplies its facts as well as its cells. The `Maybe::Some` arm
above states `fact p->value == value`, which names a constructor binding and
so travels nowhere: only `unfold` or a proof `match` names that binding. An arm
fact that names no binding of its own does travel, so a resource whose `Some`
arm also states `fact p != 0` makes that an entry premise, and a walk that
starts with `if (p == 0)` decides the guard instead of needing an infeasible
`branch`. The proof starts from the kernel's contract entry, which states
those facts, so the proof and contract certification share what the contract
assumed
(`mdtests/resource_selected_arm_fact_at_contract.md`).

### A model field is not carried for you

An instance that survives a call, a loop or an `unfold`/`fold` round trip keeps
its **identity** and not its model. Three places give it a fresh one, and each
has the same repair: say what you want kept.

- **A call that returns ownership.** `owns c: Cell()` on a callee means the
  callee may set the model however it likes, so after the call `c.rank` is a
  value the caller knows nothing about. Only the callee's own postcondition
  relates it to the entry model: `ensures c.rank == old(c.rank)`.
- **A loop that owns the instance.** A loop head is an arbitrary iteration, so the
  model a binder carries there is whatever the invariants state about it, never
  the model it held at loop entry. `invariant c.rank == old(c.rank);` is what
  carries a field through.
  A checked exit keeps the body's final model under the loop binder's name,
  including a guard-false `do ... while` exit or a `break` after refolding.
  Ownership withheld from the body is returned with that final resource
  exchange; it does not become writable inside the loop. See
  `mdtests/do_while_returns_rebound_resources.md` for returning a reconstructed
  path and an empty list while retaining a caller-owned cell.
- **`unfold` and the `fold` that answers it.** `unfold(c)` gives the instance up,
  so at the `fold` below it `c.rank` names no model at all — there is no
  instance of that identity to read. Name the value it had where it still
  existed: `let c = fold(Cell(), { rank: old(c.rank) });`, or bind it at the
  unfold, `let { rank: r } = unfold(c);`, and write `r`.

The same holds for a population count. A contract's `produces` or `consumes`
moves `count(R(a))`, and the transition relates the two counts, so an `ensures`
states that relation: `ensures count(R(a)) == old(count(R(a))) + 1`.

A refusal about any of these names the field, says which step replaced the
model, and prints the clause above for the case that applies.

### Refuting an arm

The same decision runs backwards. A folded instance's body holds wherever the
instance is held, so a premise that contradicts an arm's own binding-free fact
says the model is not that constructor. `tree_at`'s `HeapTree::Empty` arm
states `fact p == 0` and its `HeapTree::Node` arm states `fact p != 0`, so a
guard on a child link decides the child's model both ways: `root->left != 0`
publishes `left.model != HeapTree::Empty`, which is exactly the evidence arm
selection reads, and `root->left == 0` refutes the `Node` arm instead. When
refutation leaves exactly one arm and that arm's constructor carries no
fields, the model has only one value left, so the equation itself is
published and `unfold` and proof `match` have their constructor.

A premise must meet an arm's fact head-on. A known value of a pure function
over the model, such as `ctx_node_is(c.model, parent) == 1` as a section
requirement or a loop invariant, refutes no arm. Deciding it would mean
evaluating the function's body at each arm's constructor with the arm rebuilt
at symbolic bindings, and trying each such fact in turn. That is a search for
the fact that refutes an arm, and arm publication runs inside checking steps
(`unfold`, case splits, loop frontiers), which do not search
([verifier design](../internals/verifier-design.md)). On the rbtree erase
proof it cost 63,000 to 79,000 work units per held instance and never refuted
an arm. A proof that needs the exclusion states it, `have c.model !=
Context::Top by ...`, or matches the model first; the exclusion is then an
exact fact that refutation reads by lookup
(`mdtests/loop_head_predicate_does_not_decide_an_arm.md`).

Refutation is exact and does not search: each held instance's arms are visited
once, an arm goes only when one of its own binding-free facts is contradicted
by an exact fact, and each arm's binding-free clauses are evaluated once.

### Where a matched instance's arms are decided

Selection, refutation, the cells the surviving arms agree on, and the naming of
the cells an `unfold` exposes are one mechanism with one implementation. It
runs at the frontiers a proof passes through, and nowhere else. There are
eight, and every one of them decides the same way from its own premises:

| Frontier | Premises it decides from |
| --- | --- |
| contract entry lowering | the section's `requires`, and the entry resources |
| contract return | the contract's resources at the returned state |
| loop head | the loop's invariants, over the head's fresh models |
| loop back edge | the invariants, the body's effects, and the body's path facts |
| loop exit | the invariants together with the failed guard, or a `break`'s facts |
| guard conjunct | the conjuncts of a short-circuit guard already known true |
| `unfold` | the premises standing at the `unfold`, for the instance it opens and for each child it produces |
| frontier case split | the premises standing at the split, for the instance the split is about |

An exact constructor equality already decides the arm. In that case opening
its resource uses the indexed constructor evidence directly and refutes
nothing. Unknown models still use the refutation rule above.

The order inside one publication is the decision's own: refutation first,
because a refuted arm is evidence selection reads, then the read authority and
the arm's facts under the premises refutation just established. That is why a
guard conjunct that rules out an ascending frame's `Top` arm can read the cell
its two surviving arms agree on, and why an `unfold` whose arm was decided only
by refuting the others names that arm's cells exactly as an arm decided by a
`requires` does. A requirement of any shape refutes at contract entry exactly
as an invariant of that shape refutes at a loop head.

Each frontier consumes what it can use. A loop body learns what a child it
unfolded earlier is at the case split, since the guard that decides it is a
fact of the body and not of the head
(`mdtests/loop_body_refutes_an_unfolded_child.md`). An `unfold` also states the
model fact that chose the arm it opened, so the rest of the path -- including
the back edge's structural descent -- names that constructor. A loop exit is
how an ascending walk learns that the frame it is left holding is the top one:
`parent == 0` refutes every arm that states `fact parent != 0`. Contract return
publishes read authority alone, because the returned context's models are
decided at the caller's own next frontier.

While a section's clauses are still being evaluated one at a time, the cells
the premises already decide are published so each clause can be addressed; the
section's own publication is taken once, on the finished state. Re-deciding
every arm of every held instance per clause would cost the arms of the section
rather than the arms of the frontier.

The regressions are `mdtests/resource_refuted_arm_model_fact.md` for both
directions, `mdtests/loop_decreases_strict_descendant.md` for the loop
head and `mdtests/loop_ascending_walk_to_root.md` for the exit, and
[`examples/modeled-binary-tree`](https://github.com/clicklang/click/tree/master/examples/modeled-binary-tree)
is the verified walk that needs both.

An arm's cells need not hang off the resource's own parameters. A constructor
field declared `struct tag*` makes its binding a struct base for the whole
arm, so a frame keyed by one node can own the cells of another node the model
carries: `owns parent->left;`, `fact parent->left == child;`, and
`owns sibling: tree_at(parent->right);` all resolve against `struct tag`'s
layout. That is what lets a context frame own its parent's links while being
indexed by the child it focuses. A binding of any other type is not a base and
is refused as one. The regression is
`mdtests/resource_arm_binding_struct_base.md`.

An arm fact may also apply a pure function to a pointer -- the resource's own
parameter, a pointer-typed constructor binding, or both. That is how a model
states a relation between a node and one of its submodels without repeating it
in every contract: `rb_at`'s `Node` arm states
`fact rb_parent_is(left_model, p) == 1`, and folding the node re-establishes
parent/child consistency. `fold` discharges a body fact *exactly* -- the
proposition it lowers from the arm has to be an available checked fact, since a
fold proves nothing on its own -- so the term the arm lowers to and the term the
proof established have to be the same term.

They are, and that needs one rule. A pure function's pointer parameter is
lowered as an array reference, a memory with a pointer and an element
type, so that a function such as the standard library's `count(p, lo, hi, x)`
can index it. When the function's body -- and, transitively, the body of every
function it calls -- reads no C memory, its result is a function of its argument
*values* and the memory in that triple is dead weight. Such a function's
pointer arguments are therefore anchored to one canonical memory instead of
the ambient one. Without that, the same proposition would be two different terms
on either side of any C write, and a fact proved before the C runs would not
discharge the identical body fact demanded by the `fold` after it. The
classification is syntactic and conservative: a field place, an index, a
qualified global, a point-reading form such as `old(...)`, a resource field or
count, a predicate call, or a call to an undeclared function all make a function
memory-dependent, and those keep the ambient memory they have always had. The
regressions are `mdtests/fold_pointer_argument_body_fact.md` with its negative
`mdtests/fold_pointer_argument_body_fact_rejects_other_owner.md`, and
`mdtests/rb_first_last.md` for the parent/child consistency this makes
statable in the body.

A checked pointer equality also lets a fold use an available body fact under
an equal pointer form. This includes C pointers represented by a symbolic
base plus a scaled offset, both in pointer comparisons and inside pure-function
arguments. The checker looks up exact aliases only for pointers in the requested
fact, substitutes one alias, and still requires exact evidence for the
result. It neither derives a missing nonnull fact nor grants ownership through
an equality. Null itself is not used to enumerate unrelated empty links.

Naming reaches those cells too. A cell a contract `owns` is materialized at
function entry and keeps one load identity, so a fact about it survives a write
to a separately owned sibling even inside a single inlined statement
(`mdtests/guard_after_sibling_write.md`); an `unfold` names the cells it
exposes the same way, and that projection evaluates the arm's memory clauses
with the *constructor bindings* substituted as well as the resource's own
parameters. A clause written over a pointer payload therefore denotes a cell
the projection can name, whenever the selection came from a constructor premise
that says what the payload holds. Without those substitutions the clause did
not evaluate, the cell stayed unnamed, and a later C read of it across a write
to a separately owned object minted a second load identity for one cell,
leaving a guard over it undecided. The positive is
`mdtests/guard_after_sibling_write_through_unfold.md` and the whole-function
case is `mdtests/rb_replace_node.md`'s `Left` and `Right` frames. A selection
that names only the variant supplies no bindings, and a payload no premise pins
names no cell: `mdtests/guard_after_sibling_write_rejects_unknown_payload.md`.
A read through a folded instance still refuses when the arm is not selected at
all; nothing here grants ownership, which only an explicit `unfold` produces.

The ownership an arm introduces through a binding respects proved equality of
that binding, exactly as declared resource identity respects proved equality of
its arguments. A binding is a proof name: at an arbitrary frontier it is a
fresh symbolic pointer, and no C statement is written through it. Its clauses
are instantiated at the binding itself, so the cells it owns, the facts it
states and its child resources' arguments are filed under the binding's own
value, whatever equalities happen to be known. An access the program writes
another way reaches them through the equality instead: memory resolution places
an address in the owning block when the graph knows the two name one
coordinate, and store separation looks an owned member up under every base that
recorded cross-block equalities join to the store's address, proving that the
two addresses are equal and that the member contains the access before using
it. A walk that has proved `identity == parent` therefore reads through the
parameter's block a cell the frame owns at the binding
(`mdtests/binding_cell_read_through_equal_local.md`; the whole-loop case is
`mdtests/rb_ascending_walk_to_root.md`), and a store through `q->next` is kept
off a caller cell by ownership of `identity->next` two equalities away
(`mdtests/do_while_restored_field_frame_remains_separate.md`).

An `unfold` projection names the cells it exposes at the resource's own
arguments in the same way. An instance folded through an alias, such as
`tree(s)` with `s == p->right` exact, exposes cells its owner may already cache
at `p->right`, and the read through `s` resolves through the equality to the
cell already cached, one value
(`mdtests/an_unfold_through_an_alias_keeps_the_owners_cell_names.md`). A loop
invariant `n == old(n)` therefore makes `n->right` one read across the loop
body without listing the alias in a later `transport`
(`mdtests/a_retained_child_read_unfolded_at_its_older_alias_needs_no_listed_alias.md`);
a store to the field still blocks that transport
(`mdtests/a_store_to_a_retained_child_read_is_not_framed.md`).

Neither route renames a value, so lowering a clause gives the same term with or
without the equality, and every fact it produces raises. Only
recorded equalities propose a base, and the access is proved equal before it is
used, so a disequality, a disjunction, or an unproved equality changes nothing
(`mdtests/binding_cell_read_rejects_an_unproved_equality.md`), and a read at an
offset the arm does not own is still refused
(`mdtests/binding_cell_read_rejects_an_unowned_offset.md`). The lookup visits
the access's own alias class, never the other owned objects.

If a fact reads mutable memory, the composite body must contain a memory
resource covering that memory. That child is what makes the fact stable while
the resource is folded:

<!-- verified-example: mdtests/composite_resource_once_flag.md -->
```click
resource uncalled(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 0;
}
```

The coverage check can use scalar facts from the fact itself:

<!-- verified-example: mdtests/composite_resource_symbolic_fact_coverage.md -->
```click
resource indexed_zero(p: int32*, k: int32, n: int32) {
    owns p[0..n];
    fact 0 <= k and k < n and p[k] == 0;
}
```

This symbolic check proves the index is inside the range; the memory base must
still match the contained memory resource directly.

A `views` child covers a fact as well as an `owns` child does, and makes the
definition a borrowing composite: the fact holds for as long as the borrow the
body packages, and the folded head keeps that borrow open. Pure scalar facts
such as `fd >= 0` do not need a contained memory resource.

This is resource-context reasoning, not theorem application. Theorems stay
pure; `apply(theorem(...))` can add proposition facts, but it does not consume
or return resources.

This slice supports viewed and owned memory elements plus declared token and
composite resources inside composite bodies. Duplicate contained owned
resources are rejected, including resources whose arguments are provably
equal. General composite-resource cycles are rejected; guarded direct
self-recursion is the deliberate exception. Resource unfolding is explicit.
The one fold made without being written is the implicit closer's fold of the
resource the contract `produces`, on a returned path that holds its body
(`mdtests/an_omitted_proof_folds_the_resource_its_contract_produces.md`).

The smallest ownership-shaped pattern is a composite resource that bundles
several concrete memory resource facts. For example, `first_cell_copy_access(dst, src)`
can own `dst[0..1]` and view `src[0..1]`, while
`owned_one_cell(owner, data)` can contain memory resources for an owner object
and an explicitly passed buffer pointer. In this conservative shape, the resource's
parameters name the lower-level memory objects directly. More convenient
field-dependent composite resources can derive a contained buffer from
`owner->data`. The folded resource exposes derived `separate(...)` facts from
its hidden contained writes, while explicit `fact` clauses can carry additional
shape facts such as length and capacity. A push-style buffer resource can use a
stronger pre-state resource, such as `owned_buffer_with_room(owner)`, with
facts like `owner->len < owner->cap`; after the mutation, the proof can fold
back to the ordinary `owned_buffer(owner)` shape.

### Choosing resource boundaries

Composite resources should describe ownership, not every logical role that
owned memory happens to play.

Keep backing storage inside an owner-keyed resource when it stays encapsulated.
For example, the linear and wrapped states of a ring buffer can both contain
the same full-backing resource. Head and tail facts distinguish the states;
wrapping does not change which allocation the ring owns. This keeps the C API
owner-oriented and makes opaque state transitions compose naturally.

Name a backing pointer and its bounds explicitly when ownership actually
leaves the enclosing resource. A borrowed-slice operation needs stable names
for the retained prefix and suffix and for the independently owned middle
slice. Those names let owner-independent helpers use the extracted resource
and let the return operation identify the pieces it must recombine.

As a rule of thumb:

- use `fact` clauses for logical states over unchanged ownership;
- use nested resources for independently useful ownership components;
- add explicit pointer and bound parameters when a component can escape,
  split, or outlive the folded owner resource.

See `examples/ring-buffer/` for encapsulated storage and
`examples/borrowed-slice/` for extracted storage.

## Split and rejoin

A caller can pass a subrange of a larger owned memory resource:

<!-- verified-example: mdtests/resource_summary_splits_write_range.md -->
```click
int32 write_first(int32 p[]) {
    owns p[0..1];
    ...
}

int32 write_first_then_second(int32 p[]) {
    owns p[0..2];
    ...
}
```

During the call, Click splits out `p[0..1]` and keeps the residue `p[1..2]` in
the caller. When the helper returns `p[0..1]`, adjacent write ranges are
normalized back into `p[0..2]`.

The same mechanism works for symbolic one-cell subranges when current facts
prove the subrange is covered, and for a range returned over a displaced
pointer such as `x + i`, which rejoins its neighbours over `x`.

## Element width

Memory-resource ranges use the element width of the pointer expression.

For `int32 p[]`, `p[1..2]` covers one four-byte `int32` cell.

For `uint8 p[]`, `p[1..2]` covers one byte. A memory resource for `p[0..1]` does not
cover `p[1]`.

## Supported resource behavior

Click implements:

- mandatory permission checks for external loads and stores,
- viewed and owned elements over memory ranges,
- an internal memory resource family boundary for entailment, consumption,
  access authorization, splitting, and joining,
- exact-match abstract resources declared with `abstract resource name(...)`,
- exact-match declared resources with canonical owned quantities,
  unit-by-unit contract transfer, exact and wildcard population counts, and
  scoped access to shared population bodies,
- composite resources with explicit `unfold(resource)` and
  `fold(resource)` tactics, including composition over other declared
  resources,
- iterated guarded ownership in composite bodies, one fact for a bounded
  family of elements selected by owned guard cells, with `unfold` and `fold`
  steps for single slots and whole clauses, plus a store rule for the guard cells,
- one-step fact views for folded composite resources, plus
  `observe(resource)` tactics that explicitly record fact-view projection
  without exposing contained owned resource facts,
- checked lending of owned memory to satisfy a viewed requirement, with scoped
  recovery at the return,
- visible owned resources imply `separate(...)` facts; provably overlapping
  visible writes are rejected. A `have separate(memory(...), memory(...))`
  can select two distinct owned fields exposed by independent named-resource
  unfolds from the current ownership partition. The same `have` selects
  any two different resources the state owns exactly as written, such as
  a resource instance the proof just folded and a cell owned beside it;
  only a memory operand may instead lie inside a larger owned range. A
  viewed field or two references to the same owned field cannot justify
  that separation,
- composite resources project direct `contains(parent, child)` facts for owned
  contained resources and direct `separate(child1, child2)` facts for owned
  sibling resources without exposing the hidden owned resource facts,
- shared read borrows whose covered memory stays unchanged and allocated,
  including partial ranges, composite frontiers, and a composite that packages
  a borrow and outlives the call that produced it,
- linear write transfer through function summaries,
- covered subrange splitting and adjacent range rejoining,
- fixed- or runtime-sized heap allocation authority through the built-in owned
  `allocation(base, bytes)` resource, and
- complete-access `free`, ended allocation lifetimes, double-free/use-after-free
  rejection, and verified-exit leak checks.

Not implemented yet:

- fractional permissions,
- general C allocation APIs beyond the modeled struct, scalar-buffer, and
  pointer-array forms, plus other unsupported allocator forms,
- custom resource-family algebra,
- implicit resource unfold/fold search beyond the implicit closer's fold of a
  produced resource,
- persistent token resources,
- ownership predicates,
- explicit resource algebra tactics,
- general mutable spec/model state.

The current resource layer is intentionally small. Its memory family is the
foundation for broader memory-permission logic, not the final ownership model.

For the planned relationship between population counts, access authority,
and mutexes, see the internal
[resource invariant design](../internals/resource-invariants.md). That record
separates implemented sequential checks from future concurrency rules.

A helper can also compose two independent unit births while consuming and
returning their ordinary authority-bearing controls. Each returned control
must preserve its input's anchor and authority scopes; each new member needs
its corresponding input authority. The checked ledger still verifies both
births and exact returned custody. This bounded composition adds no creation
right for an external pointer. `authority_two_control_birth_helpers.md` checks
two initializer calls, and its extra-member companion rejects closing a
control whose capacity no longer equals its population. Grouped symbolic
quantities and arbitrary collections of effects remain unsupported.
