# Permissions

Permissions describe what external memory a proof may access. In the proof
context, permissions are resource facts. They sit alongside pure facts such as
integer bounds, but they obey resource-composition rules because some
permissions must not be copied freely.

Click currently has two first-layer memory permissions:

```click
views p[0..1];
consumes p[0..1];
```

These clauses create resource facts in the verifier's resource context. External C
memory accesses must be covered by the current resource context:

- a load requires a viewed or owned memory resource,
- a store requires an owned memory resource,
- local stack memory does not require a resource.

## Resource Context And Families

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

In the first-layer model, the viewed element is the stable read view of memory.
Algebraically, it is the core of the owned element:

```text
core(own(memory(p[lo..hi]))) = view(memory(p[lo..hi]))
core(view(memory(p[lo..hi]))) = view(memory(p[lo..hi]))
```

The Click surface requests these elements with `owns`/`consumes`/`produces` and
`views` respectively.

That is why owned memory can satisfy viewed requirements without consuming the
owned element.

This resource-family boundary is intentionally more general than memory
ownership. Click also has exact-match user-defined resources, which can model
API protocols without forcing those protocols to look like heap cells.

## Loadability And Authority

`loadable(...)` and permissions still answer different questions, but access
permissions include the loadability needed for the covered access.

`loadable(p[0..n])` says the range is loadable. It is about
memory safety and bounds.

`views p[0..n]` or `owns p[0..n]` says the current code has authority to access
that range. It is about permission.

For an external read, `views` is normally enough:

```click
int32 first(int32 p[]) {
    views p[0..1];

    ensures result == p[0] by auto;
}
```

Similarly, an owned memory resource grants authority to store and makes the
covered range loadable. Use `loadable(...)` separately when you need to prove memory exists
without granting read or write authority, or when a larger structural bound is
useful for index reasoning.

When the same loadability fact must appear as a proposition, use
`loadable(segment)`. This is common in composite resource definitions, where
`fact` clauses are pure propositions rather than structural requirements.

## Viewed Memory

`views` permits loads. It does not permit stores. While no write to the
same cell occurs in the current execution, repeated reads of that cell are
stable: they produce the same symbolic value.

```click
int32 peek(int32 p[]) {
    views p[0..1];
}
```

Viewed resources are copyable across function calls. If a caller owns
`p[0..1]`, it may satisfy a helper's `views p[0..1]` requirement and still keep
its owned element afterward. This is a call-scoped borrow: satisfying the
callee's `views` clause does not add a new persistent view to the caller when
the call returns. A view that the caller already held is different—it remains
in the caller's resource context until explicitly transferred or consumed.

This distinction matters at deallocation. `free` requires allocation authority
and complete owned access, then rejects any other direct or composite resource
that may still refer to the retired allocation. A scoped call borrow has ended
and therefore does not block `free`; a pre-existing persistent view does block
it locally. A view proved separate from the freed allocation survives.

## Owned Memory

An owned memory resource permits both loads and stores and entails its viewed
core. Stores update the symbolic memory state; later reads of the same cell see
the written value unless a later write changes it again.

```click
int32 set_one(int32 p[]) {
    owns p[0..1] by auto;
}
```

Owned memory resources are linear across function calls. `owns` transfers the
resource to the callee and returns it; `consumes` transfers it without returning
it. The caller cannot use a consumed resource afterward.

This is the main difference between a permission and an ordinary proposition.
Ordinary facts can be used repeatedly. An owned resource can be transferred.

## Function Calls

Function calls use the callee's verified contract as an opaque summary:

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

An opaque call first creates proof obligations for the callee's `requires`
clauses. Those requirements are then available as established assumptions while
Click evaluates the remaining resource, effect, and postcondition clauses of
that same contract. A requirement such as `1 <= n` can therefore justify a
later footprint rooted at `p + (n - 1)`.

An unannotated callee receives no external memory permission, even if the
caller has permissions in its own context. Explicit `mutable` clauses provide
the precise abstract write footprint. Without one, an owned input resource is
used as a conservative mutable footprint.

Loads outside that footprint are preserved across the opaque call. This
includes adjacent struct fields and composes across several calls, so callers
do not need to save and restore unchanged metadata merely to give it a stable
proof spelling. Expansion exposes only ordinary source-level premises such as
the relevant `loadable(...)` range; call-havoc identities remain internal.
Preserving a dependent load such as `owner->data[i]` additionally requires the
address inputs (`owner->data` and `i`) and the target range to remain stable.
If any mutable range may overlap the loaded field, Click does not transport the
equality.

Opaque summaries support comparison, logical, quantified, predicate-call,
`separate(...)`, `contains(...)`, and `loadable(...)` propositions, including
`old(...)` and `at(function.entry, ...)`. A contract containing a snapshot of
an internal statement or loop point can still be verified directly, but that
snapshot is not visible at an opaque call site. Calling such a function reports
that its contract cannot be exposed opaquely rather than reporting a dependency
ordering error.

## Token Resources

You can declare an exact-match resource:

```click
resource open_fd(fd: int32);
```

Then a contract can require and return instances of that resource:

```click
int32 borrow_fd(int32 fd) {
    owns open_fd(fd) by auto;
}
```

A token resource is transferred by function calls. If a callee `owns
open_fd(fd)`, the caller gets the token back. If the callee `consumes
open_fd(fd)`, the caller loses the token.

Token resources currently have exact-match behavior only. They do not split,
rejoin, imply other resources, authorize C statements, or define custom algebra
rules. Resource arguments currently support current-state C expressions such as
parameters, constants, arithmetic, pointer expressions, and indexes. Arguments
are checked against the types declared in the resource definition.

Token resources are nonduplicable exact-match capabilities. A resource context
cannot contain the same owned token resource twice: duplicate clauses such as
two `consumes open_fd(fd);` entries are rejected, and a call cannot satisfy
two callee resource parameters with the same token.

## Counted Resources

Use `counted resource` when several indistinguishable, independently
consumable units of the same capability may coexist:

```click
counted resource object_ref(object: struct object*);
```

Unlike an ordinary token, `object_ref(object)` may appear more than once in a
resource context. Click stores equal owned units as one canonical fact with a
quantity. A contract clause transfers one unit: consuming one
`object_ref(object)` from a quantity of two leaves one unit behind. Viewed
facts remain idempotent and do not carry a count.

This first counted-resource layer only represents and transfers quantities. It
does not let a proof mint another unit from one existing unit. In particular,
declaring a resource counted is not by itself a proof of a C `retain`
operation. Connecting capability creation and final release to a concrete
reference-count field requires an additional invariant tying the counted
capabilities to that authoritative C state.

Counted declarations are atomic and therefore end in `;`; composite resource
bodies remain exclusive.

A function spec may exist only to consume a resource:

```click
resource can_complete(cb: int32);

int32 complete(int32 cb) {
    consumes can_complete(cb);
}
```

That spec contributes a call summary. Calling `complete(cb)` consumes
`can_complete(cb)`, so a second call on the same path fails unless some other
contract returns the resource.

## Composite Resources

Declarations with a body define composite resources. The body is a one-layer
definition: it names contained resource facts and pure facts that justify the
abstract resource fact.

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
consumes `live_fd(fd)`, and neither step unfolds owned permissions. This
one-step behavior is intentional: large composite resources should not be
recursively expanded by default proof automation.

A guarded directly recursive resource also has a finite inductive witness.
`decreases resource list(node)` can use a direct contained child as a hidden
structural rank for a directly recursive C traversal. This does not turn
pointers into sizes and does not automatically unfold the resource: the proof
still uses `observe` or `unfold` to expose the layer it needs, while the
termination checker independently rechecks the declared child against the
exact resource definition. The recursive call path must establish the resource
guard (for example, `node != 0` or the equivalent nonnull arm of
`if (!node)`), either from an entry requirement or from C control flow. The
ordinary partial-correctness proof checks resource transfer,
so the traversal may consume and deallocate nodes after descending.

When code needs the contained owned resources, use `unfold(resource)`. When
the proof has rebuilt the body, use `fold(resource)`:

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

### Conditional And Recursive Bodies

A composite resource may put its entire body under one load-free `if`:

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        contains list(node->next);
    }
}
```

The false case is an empty body; conditional resource bodies have no `else`.
The condition must not read memory. This avoids circular reasoning in which a
load is used to decide whether the permission authorizing that load exists.

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

If a fact reads mutable memory, the composite body must contain write
permission covering that memory. This is what makes the fact stable while
the resource is folded:

```click
resource uncalled(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 0;
}
```

The coverage check can use scalar facts from the fact itself:

```click
resource indexed_zero(p: int32*, k: int32, n: int32) {
    owns p[0..n];
    fact 0 <= k and k < n and p[k] == 0;
}
```

This symbolic check proves the index is inside the range; the memory base must
still match the contained owned memory resource directly.

`views flag[0..1]` is not enough for this purpose. A viewed resource authorizes
inspection but does not prevent another holder of write permission from
changing the cell. Pure scalar facts such as `fd >= 0` do not need a contained
memory resource.

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
several concrete permissions. For example, `first_cell_copy_access(dst, src)`
can own `dst[0..1]` and view `src[0..1]`, while
`owned_one_cell(owner, data)` can contain permission for an owner object and an
explicitly passed buffer pointer. In this conservative shape, the resource's
parameters name the lower-level memory objects directly. More convenient
field-dependent composite resources can derive a contained buffer from
`owner->data`. The folded resource exposes derived `separate(...)` facts from
its hidden contained writes, while explicit `fact` clauses can carry additional
shape facts such as length and capacity. A push-style buffer resource can use a
stronger pre-state resource, such as `owned_buffer_with_room(owner)`, with
facts like `owner->len < owner->cap`; after the mutation, the proof can fold
back to the ordinary `owned_buffer(owner)` shape.

### Choosing Resource Boundaries

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

## Split And Rejoin

A caller can pass a subrange of a larger owned memory resource:

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

## Element Width

Permission ranges use the element width of the pointer expression.

For `int32 p[]`, `p[1..2]` covers one four-byte `int32` cell.

For `uint8 p[]`, `p[1..2]` covers one byte. Permission for `p[0..1]` does not
cover `p[1]`.

## What Exists Today

Implemented today:

- mandatory permission checks for external loads and stores,
- viewed and owned elements over memory ranges,
- an internal memory resource family boundary for entailment, consumption,
  access authorization, splitting, and joining,
- exact-match token resources declared with `resource name(...)`,
- counted exact-match resources declared with `counted resource name(...)`,
  with canonical owned quantities and unit-by-unit contract transfer,
- composite resources with explicit `unfold(resource)` and
  `fold(resource)` tactics, including composition over other declared
  resources,
- one-step fact views for folded composite resources, plus
  `observe(resource)` tactics that explicitly record fact-view projection
  without exposing contained permissions,
- owned memory implying viewed authority,
- visible owned resources imply `separate(...)` facts; provably overlapping
  visible writes are rejected,
- composite resources project direct `contains(parent, child)` facts for owned
  contained resources and direct `separate(child1, child2)` facts for owned
  sibling resources without exposing the hidden permissions,
- copyable read transfer,
- linear write transfer through function summaries,
- covered subrange splitting and adjacent range rejoining,
- fixed- or runtime-sized heap allocation authority through the built-in owned
  `allocation(base, bytes)` resource, and
- complete-access `free`, retired lifetimes, double-free/use-after-free
  rejection, and verified-exit leak checks.

Not implemented yet:

- fractional permissions,
- general C allocation APIs beyond exact struct allocation, runtime-sized
  `int32` arrays, and `free`,
- custom resource-family algebra,
- implicit resource unfold/fold search in `auto`,
- persistent token resources,
- ownership predicates,
- explicit resource algebra tactics,
- general mutable spec/model state.

The current permission layer is intentionally small. It should be treated as the
foundation for broader permission logic, not as the final ownership model.
