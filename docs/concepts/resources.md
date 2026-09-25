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

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
views p[0..1];
consumes p[0..1];
```

These clauses create resource facts in the verifier's resource context. External C
memory accesses must be covered by the current resource context:

- a load requires a viewed or owned memory resource,
- a store requires an owned memory resource,
- local stack memory does not require a resource.

## Resource context and families

Internally, Click represents resource facts as `CResourceFact` values. A
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

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 first(int32 p[]) {
    views p[0..1];

    ensures result == p[0] by auto;
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

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 peek(int32 p[]) {
    views p[0..1];
}
```

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
ownership already authorizes the read, however the address is spelled.

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

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 set_one(int32 p[]) {
    owns p[0..1] by auto;
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

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 helper(int32 p[]) {
    owns p[0..1] by auto;
}

int32 caller(int32 p[]) {
    owns p[0..1] by auto;
}
```

The caller must have a resource that covers every callee resource requirement.
`step()` checks the pure and resource preconditions, advances across the
entire call, transfers the declared resources, applies the memory effect, and
adds the pure postconditions. It does not execute the callee body. The callee
must therefore have been verified earlier in the file; otherwise Click reports
that its contract has not been verified yet. A viewed range rooted in a caller
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
explicit program-point snapshots. Expansion spells the chain with source C
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
carries the fields `start` and `end` and owns `object(region)`, so a contract
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

The publication is read authority and nothing more. The instance stays folded,
so a store to a cell it owns is refused until an explicit `unfold` moves the
cell into the proof state, and a cell the body does not own is not published
at all. This publication belongs to the contract's own clauses at its entry
and return; it is not one of the frontiers where a matched instance's arms
are decided, so a loop head does not read through a folded field-bearing
instance. The regressions are
`mdtests/contract_owns_through_field_bearing_instance.md` (both clause
orders), `mdtests/contract_returns_field_bearing_sibling.md` (both clause
orders), `mdtests/call_through_field_bearing_sibling.md` (a caller applying
such a contract), `mdtests/contract_postcondition_reads_through_field_bearing_instance.md`,
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
same way in either spelling.

An unannotated callee receives no external memory permission, even if the
caller has permissions in its own context. The callee's owned resources provide
the precise abstract write footprint. Without one, an owned input resource is
used as a conservative write footprint.

Loads outside that footprint are preserved across the opaque call. This
includes adjacent struct fields and composes across several calls, so callers
do not need to save and restore unchanged metadata merely to give it a stable
proof spelling. Expansion exposes only ordinary source-level premises such as
the relevant `viewable(...)` range; call-havoc identities remain internal.
Preserving a dependent load such as `owner->data[i]` additionally requires the
address inputs (`owner->data` and `i`) and the target range to remain stable.
If any owned range may overlap the loaded field, Click does not transport the
equality.

Opaque summaries support comparison, logical, quantified, predicate-call,
`separate(...)`, `contains(...)`, and `viewable(...)` propositions, including
`old(...)` and `at(function.entry, ...)`. A contract containing a snapshot of
an internal statement or loop program point can still be verified directly, but that
snapshot is not visible at an opaque call site. Calling such a function reports
that its contract cannot be exposed opaquely rather than reporting a dependency
ordering error.

## Abstract resources

You can declare an exact-match abstract resource:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
abstract resource open_fd(fd: int32);
```

Then a contract can require and return instances of that resource:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 borrow_fd(int32 fd) {
    owns open_fd(fd) by auto;
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

Equal declared resources accumulate as an exact quantity. Duplicate clauses
such as two `consumes open_fd(fd);` entries require two units, and a call cannot
satisfy that requirement with one unit.

## Resource quantities

Every declared resource can have several independently consumable units with
the same arguments:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
abstract resource object_ref(object: struct object*);
```

Click stores equal owned units as one canonical fact with a quantity. A clause
without a coefficient transfers one unit: consuming one `object_ref(object)`
from a quantity of two leaves one unit behind. An owned user-declared resource
may use `owns amount of object_ref(object)`, `consumes amount of ...`, or
`produces amount of ...` to transfer a runtime `int32` quantity algebraically.
The coefficient must be proved nonnegative at the contract snapshot, and zero
grants no authority. Viewed facts remain idempotent and do not carry a count.

Symbolic coefficients are rejected for memory, allocation, and recursively
defined composite resources. Those families need distinct semantics; Click
does not interpret a symbolic coefficient by expanding it into repeated facts.

`count(object_ref(object))` observes the exact quantity. A resource body may
relate that count to C state and belongs to the population as a whole, not to
each unit. `open(object_ref(object)) { ... }` exposes that shared body for a
scoped proof and requires it to be restored. Declaring a resource does not by
itself justify minting a unit; retain and release contracts must preserve the
body invariant while changing both the C state and logical quantity.

Inside `count(...)`, `_` is a wildcard over one resource argument. For example,
`count(pool_object(pool, _))` sums all exact object populations for `pool`.

A count is a nonnegative number that fits in an `int32`, and Click holds
contracts to that. Wherever two quantities for one population are added — two
clauses of one contract, two facts in one state, two entries under one
wildcard — the total has to be one Click can state exactly, or the two
quantities stay separate and the contract that needs them added is refused.
Constant quantities are added when their sum fits, and a quantity split off a
population recombines with its own remainder. Without that rule, `produces
2000000000 of tok(o)` twice composed to a population of `-294967296`, and
`ensures count(tok(o)) < 0` was provable of a function that had just produced
four billion units.

A function spec may exist only to consume a resource:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
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

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
resource nonnegative_fd(fd: int32) {
    fact fd >= 0;
}

resource live_fd(fd: int32) {
    contains nonnegative_fd(fd);
}
```

A function that holds `live_fd(fd)` owns the folded abstract resource. It does
not automatically get every nested fact. `observe(resource)` takes one
non-consuming view step:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 return_fd(int32 fd) {
    owns live_fd(fd) by auto;

    ensures result >= 0 by {
        observe(live_fd(fd));
        observe(nonnegative_fd(fd));
        execute();
        simp();
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
identity, so it stays tied to the loan it was read through.

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

A child named through a `let` witness has no C spelling, so the checker
cannot compare it with the call's argument syntactically. It instead
instantiates the exact definition over a symbolic entry state: the guard and
the witness's `where` facts are assumed, the call's argument is evaluated in
that state, and the pure kernel must decide that the argument is the witness
pointer. In the marked list, `(struct node *)(node->word & ~1)` is the
witness because the `where` fact and the alignment evidence determine it.
Loads on the call path are the same uninterpreted reads the syntactic
comparison relies on; the ordinary contract proof remains responsible for
the actual resource the call receives.

When code needs the contained owned resources, use `unfold(resource)`. When
the proof has rebuilt the body, use `fold(resource)`:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
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
        execute();
        fold(called(flag));
    }

    ensures result == 1 by {
        unfold(uncalled(flag));
        execute();
        fold(called(flag));
        simp();
    }
}
```

`unfold(uncalled(flag))` consumes the folded `uncalled(flag)` resource and adds
the contained owned memory resource for `flag[0..1]` to the proof state. The C
execution can then mutate the flag. The execution establishes the `called`
body's exact fact; `fold(called(flag))` checks it, consumes the contained owned
resource, and adds the folded `called(flag)` resource. If a body fact needs
derivation, state it first with `have ... by { ... }`; `fold` itself does not
invoke `simp`. The end of the `by { ... }` block checks the overall claim.

`fold` also builds a composite resource from lower-level resources at a
function boundary:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 init_once(int32 flag[]) {
    consumes flag[0..1];

    produces uncalled(flag) by {
        execute();
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
instead of relying on `auto` to search through every possible nested body.

### Borrowing a composite

`views` of a composite covers its checked one-level frontier. Lending one puts
the folded head in escrow and protects the direct memory children the
definition names; a contained composite becomes a read-only description under
the same borrow. Reading further down is projection: `unfold`, `observe`, and
`open` of a borrowed composite add the child to the borrow's permitted
descriptions after the kernel rechecks that the definition contains it. A
projection exposes nothing owned, so the depth a proof reaches costs nothing in
authority.

A fact in a lent body is stable for the whole borrow, because recovery restores
the exact head that was escrowed rather than refolding it. Two body shapes
cannot promise that and are refused when lent: a counted population, whose
units another call may consume, and a definition whose facts claim that storage
the body does not own is still live.

A contract cannot lend a composite and own a piece of it at the same time. An
`owns` clause naming a cell inside a composite the same contract views is
refused as a proven overlap. Write a narrow effect as ownership of the whole
composite plus an `ensures` about the cells the function leaves alone.

A composite whose definition body contains a `views` clause is a struct holding
a borrow — a cursor, an iterator, a parser over input it does not own. Folding
one makes the folded head a dependency of the borrow behind its viewed pieces,
so the lender recovers its memory only once the composite is unfolded or
consumed. A function may produce such a composite over one of its own viewed
inputs: that input's borrow stays open past the return with the produced
composite holding it, and the caller recovers the input when it consumes the
composite. Click infers the relationship when exactly one viewed input can back
the piece and refuses the contract when none or several can.

A counted population is the exception to all of this. Its body belongs to the
population rather than to each unit, so a population body that views memory is
read as an observation supported by whatever holds that memory, and folding a
unit places no hold. Lending a unit of a bodyless token population leaves the
remaining units usable.

A resource body may place `guarded_by object->mutex;` after any field
declarations to identify the C mutex intended to guard the whole body. The
modeled pthread runtime accepts this for an exclusive, unmatched resource:
initialization escrows a folded instance, locking transfers it to the current
execution path, and unlocking requires it folded again. In an execution proof,
`held(&object->mutex)` states whether that path owns the lock guard; it does
not by itself grant the protected resource.

A contract clause speaks about parameters, so `consumes t: tree_at(root);`
names the tree at the entry argument. These tactics are not contract clauses:
they name the state the execution has reached. After `root = root->left` a
`fold(ctx_at(root), ...)` is the frame of the node the proof is standing on,
and a body fact such as `fact parent->left == child` instantiates to the link
the body just walked. The fold's field values are read the same way, so one
tactic never straddles two states
(`mdtests/fold_argument_reads_current_cursor.md`).

### Conditional and recursive bodies

A composite resource may put its entire body under one load-free `if`:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns &node->next;
        contains list(node->next);
    }
}
```

The false case is an empty body; conditional resource bodies have no `else`.
The condition must not read memory. This avoids circular reasoning in which a
load is used to decide whether the memory resource authorizing that load
exists.

A guarded body may contain itself directly. `unfold(list(node))` exposes one
nonnull node and the still-folded `list(node->next)` tail; `fold` performs the
reverse step. Unknown guards remain opaque to observation and automatic
resource expansion, while explicit `fold` and `unfold` report that the guard
must first be proved true or false. Unguarded self-recursion and mutual
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

- `take(data[j..j + 1])` moves element `j` out while its guard is known true;
  the fact then makes no claim about `j`, and the element is ordinary owned
  memory that C can write.
- A C store to a guard cell is allowed only where the fact claims nothing:
  at an index taken out, whose guard is known false, or whose element the
  context owns outright. Marking a taken-out cell occupied (`occupied[j] =
  1`) closes the gap, because the guard is now false and the fact owes
  nothing for `j`. Clearing a cell whose element the caller owns
  (`occupied[j] = 0`) opens one, which `give(data[j..j + 1])` closes by moving
  the element back.
- `gather` and `scatter` convert between the fact and the range its elements
  cover when a quantified fact decides every guard, which is what an
  initializer that zeroes the map needs.

No step visits the range. `take` reads one guard cell; a loop that claims a
run of `M` cells does `M` such steps; folding and unfolding the declaring
resource move one fact. Because the free cells are simply the cells whose
flag is clear, freeing two regions and reusing them for a larger run needs no
merge step (`mdtests/iterated_ownership_coalescing.md`). The language
reference lists the declaration rules and the exact step conditions under
[Iterated guarded
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
`branch`. Contract certification derives the same facts at its own entry state
rather than accepting them from the checked execution, so the two contexts
agree on what the contract assumed
(`mdtests/resource_selected_arm_fact_at_contract.md`).

### A model field is not carried for you

An instance that survives a call, a loop or an `unfold`/`fold` round trip keeps
its **identity** and not its model. Three places give it a fresh one, and each
has the same repair: say what you want kept.

- **A call that returns ownership.** `owns c: Cell()` on a callee means the
  callee may set the model however it likes, so after the call `c.rank` is a
  value the caller knows nothing about. Only the callee's own postcondition
  relates it to the entry model: `ensures c.rank == old(c.rank)`.
- **A loop that owns the instance.** A loop head is an arbitrary visit, so the
  model a binder carries there is whatever the invariants state about it, never
  the model it held at loop entry. `invariant c.rank == old(c.rank);` is what
  carries a field through.
- **`unfold` and the `fold` that answers it.** `unfold(c)` gives the instance up,
  so at the `fold` below it `c.rank` names no model at all — there is no
  instance of that identity to read. Name the value it had where it still
  existed: `let c = fold(Cell(), { rank: old(c.rank) });`, or bind it at the
  unfold, `let { rank: r } = unfold(c);`, and write `r`.

The same holds for a counted population. A contract's `produces` or `consumes`
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

A premise need not meet an arm's fact head-on. When a pure function over the
model has a known value -- `ctx_node_is(c.model, parent) == 1` as a section
requirement or a loop invariant -- refutation asks what that function's
declared body returns at each arm's constructor, with the arm's bindings
symbolic and the arm's own facts in force. An arm whose answer cannot be the
known value is refuted. This is what lets a model keyed by its own payload be
decided from a C local: the frame's facts speak about `identity`, the guard
speaks about `parent`, and the predicate is the statement that relates them.
`ctx_node_is`'s body at `Context::Top` is `if parent == 0 { 1 } else { 0 }`, so
a guard that holds `parent != 0` refutes `Top`; its body at
`Context::Left(identity, ..)` is `if identity == parent { 1 } else { 0 }`, and
the arm's own `fact identity != 0` refutes that arm once the guard has failed
with `parent == 0`. Only a declared body the kernel can evaluate to one
unconditional value takes part, and an arm binding a mathematical `Integer`
takes part in neither direction. The regressions are
`mdtests/loop_head_predicate_refutes_an_arm.md` for a field-free arm,
`mdtests/contract_predicate_refutes_a_framed_arm.md` for an arm with bindings,
and `mdtests/loop_head_predicate_does_not_decide_an_arm.md` for a predicate
that is the same at both constructors and therefore refutes nothing.

Both directions are exact. An arm goes only when the predicate's value at that
constructor, or one of the arm's own facts, is contradicted by a premise the
frozen checkers already decide; a body this kernel cannot evaluate, an arm
whose clauses it cannot bind, and a premise of any other shape all leave the
arm standing.

This is a decision, not a search: each held instance's arms are visited once,
each arm's own clauses are evaluated once, and each predicate premise about
that exact model is read once.

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
directions, `mdtests/loop_head_refuted_arm_closes_the_match.md` for the loop
head and `mdtests/loop_ascending_walk_to_root.md` for the exit,
`mdtests/arm_publication_sites.md` for the same refutation stated at each of
the eight frontiers, and
[`examples/modeled-binary-tree`](https://github.com/lacker/click/tree/master/examples/modeled-binary-tree)
is the verified walk that needs both.

An arm's cells need not hang off the resource's own parameters. A constructor
field declared `struct tag*` makes its binding a struct base for the whole
arm, so a frame keyed by one node can own the cells of another node the model
carries: `owns &parent->left;`, `fact parent->left == child;`, and
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
lowered as an array reference, a memory snapshot with a pointer and an element
type, so that a function such as the standard library's `count(p, lo, hi, x)`
can index it. When the function's body -- and, transitively, the body of every
function it calls -- reads no C memory, its result is a function of its argument
*values* and the snapshot in that triple is dead weight. Such a function's
pointer arguments are therefore anchored to one canonical snapshot instead of
the ambient one. Without that, the same proposition would be two different terms
on either side of any C write, and a fact proved before `execute()` would not
discharge the identical body fact demanded by the `fold` after it. The
classification is syntactic and conservative: a field place, an index, a
qualified global, a snapshot selector such as `old(...)`, a resource field or
count, a predicate call, or a call to an undeclared function all make a function
memory-dependent, and those keep the ambient snapshot they have always had. The
regressions are `mdtests/fold_pointer_argument_body_fact.md` with its negative
`mdtests/fold_pointer_argument_body_fact_rejects_other_owner.md`, and
`mdtests/rb_at_link_helpers.md` and `mdtests/rb_first_last.md` for the
parent/child consistency this makes statable in the body.

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
fresh symbolic pointer, and no C statement is written through it. When an
*exact* pointer equality identifies it with another pointer — the local an
ascending walk reassigns, a parameter, a witness — the arm's clauses are
instantiated at that pointer, so the cells the arm owns, the facts it states,
its child resources' arguments, and the body a later `fold` requires all land
on the address the program names. Without it a walk that has proved `identity
== parent` still reads through the parameter's block while the frame owns the
binding's, and the read is refused with `missing resource fact views
symbolic-pointer:…` with ownership of that very cell one provable equality
away. The reduction is `mdtests/binding_cell_read_through_equal_local.md` and
the whole-loop case is `mdtests/rb_ascending_walk_to_root.md`, whose every
iteration reads its frame through the C local the loop reassigns.

Exactness is the whole of the soundness argument. Only an assumed
`PointerEqual` fact counts, read from the index that files those facts under
each side, so a disequality, a disjunction, or an equality some heuristic could
derive changes nothing
(`mdtests/binding_cell_read_rejects_an_unproved_equality.md`). Two spellings of
one address are exchanged and nothing else: an equality between two offsets of
one block never becomes a `PointerEqual` in the first place, so the arm's
clauses keep the offsets they state and a read at any other offset is still
refused (`mdtests/binding_cell_read_rejects_an_unowned_offset.md`). The lookup
is keyed by the pointer and takes one hop, so a binding costs one indexed
query and no equality graph is walked.

If a fact reads mutable memory, the composite body must contain a memory
resource covering that memory. That child is what makes the fact stable while
the resource is folded:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
resource uncalled(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 0;
}
```

The coverage check can use scalar facts from the fact itself:

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
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
self-recursion is the deliberate exception. Resource unfolding is explicit;
`auto` does not yet choose unfold/fold steps on its own.

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

<!-- verified-example: mdtests/composite_resource_composes_token.md -->
```click
int32 helper(int32 p[]) {
    owns p[0..1] by auto;
}

int32 caller(int32 p[]) {
    owns p[0..2] by auto;
}
```

During the call, Click splits out `p[0..1]` and keeps the residue `p[1..2]` in
the caller. When the helper returns `p[0..1]`, adjacent write ranges are
normalized back into `p[0..2]`.

The same mechanism works for symbolic one-cell subranges when current facts
prove the subrange is covered.

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
  family of elements selected by owned guard cells, with checked `take`,
  `give`, `gather`, and `scatter` steps and a store rule for the guard
  cells,
- one-step fact views for folded composite resources, plus
  `observe(resource)` tactics that explicitly record fact-view projection
  without exposing contained owned resource facts,
- checked lending of owned memory to satisfy a viewed requirement, with scoped
  recovery at the return,
- visible owned resources imply `separate(...)` facts; provably overlapping
  visible writes are rejected,
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
- implicit resource unfold/fold search in `auto`,
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
