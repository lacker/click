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
- whether a resource is copyable or linear,
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
its owned element afterward.

## Owned Memory

An owned memory resource permits both loads and stores and entails its viewed
core. Stores update the symbolic memory state; later reads of the same cell see
the written value unless a later write changes it again.

```click
int32 set_one(int32 p[]) {
    consumes p[0..1];

    produces p[0..1] by auto;
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
    consumes p[0..1];
    produces p[0..1] by auto;
}

int32 caller(int32 p[]) {
    consumes p[0..1];
    produces p[0..1] by auto;
}
```

The caller must have a resource that covers every callee resource requirement.
`execute_step()` checks the pure and resource preconditions, advances across the
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

An opaque call first creates proof obligations for the callee's `requires`
clauses. Those requirements are then available as established assumptions while
Click evaluates the remaining resource, effect, and postcondition clauses of
that same contract. A requirement such as `1 <= n` can therefore justify a
later footprint rooted at `p + (n - 1)`.

An unannotated callee receives no external memory permission, even if the
caller has permissions in its own context. Explicit `mutable` clauses provide
the precise abstract write footprint. Without one, an owned input resource is
used as a conservative mutable footprint.

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
    consumes open_fd(fd);

    produces open_fd(fd) by auto;
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

Token resources are strict tokens. A resource context cannot contain the
same token resource twice: duplicate clauses such as two
`consumes open_fd(fd);` entries are rejected, and a call cannot satisfy two
callee resource parameters with the same token.

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
    consumes live_fd(fd);

    ensures result >= 0 by {
        observe(live_fd(fd));
        observe(nonnegative_fd(fd));
        execute_rest();
        simp();
    }

    produces live_fd(fd) by auto;
}
```

The first `observe` exposes a viewed `nonnegative_fd(fd)` resource. The second
`observe` exposes that resource's immediate fact, `fd >= 0`. Neither step
consumes `live_fd(fd)`, and neither step unfolds owned permissions. This
one-step behavior is intentional: large composite resources should not be
recursively expanded by default proof automation.

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
        execute_rest();
        fold(called(flag));
    }

    ensures result == 1 by {
        unfold(uncalled(flag));
        execute_rest();
        fold(called(flag));
        simp();
    }
}
```

`unfold(uncalled(flag))` consumes the folded `uncalled(flag)` resource and adds
the contained owned memory resource for `flag[0..1]` to the proof state. The C
execution can then mutate the flag. `fold(called(flag))` proves the `called`
body's fact, consumes the contained owned resource, and adds the folded `called(flag)`
resource. The end of the `by { ... }` block checks the overall claim.

`fold` also builds a composite resource from lower-level resources at a
function boundary:

```click
int32 init_once(int32 flag[]) {
    consumes flag[0..1];

    produces uncalled(flag) by {
        execute_rest();
        fold(uncalled(flag));
    }
}
```

Together, the three resource proof steps are deliberately local:

- `observe(resource);` exposes one immediate view layer and consumes nothing.
- `unfold(resource);` consumes one owned composite resource and exposes its
  immediate body.
- `fold(resource);` consumes one immediate body and produces the owned
  composite resource.

These steps are bounded by design. A proof that needs facts inside a nested
composite resource should name the path with repeated `observe(...)` steps
instead of relying on `auto` to search through every possible nested body.

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

This first slice supports viewed and owned memory elements plus exact-match
token resources inside composite bodies. Duplicate contained resource
tokens are rejected, and composite-resource cycles are rejected. Resource
unfolding is explicit; `auto` does not yet choose unfold/fold steps on its own.

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

## Split And Rejoin

A caller can pass a subrange of a larger owned memory resource:

```click
int32 helper(int32 p[]) {
    consumes p[0..1];
    produces p[0..1] by auto;
}

int32 caller(int32 p[]) {
    consumes p[0..2];
    produces p[0..2] by auto;
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
- composite resources with explicit `unfold(resource)` and
  `fold(resource)` proof steps, including composition over other declared
  resources,
- one-step fact views for folded composite resources, plus
  `observe(resource)` proof steps that explicitly record fact-view projection
  without exposing contained permissions,
- owned memory implying viewed authority,
- visible owned resources imply `separate(...)` facts; provably overlapping
  visible writes are rejected,
- composite resources project direct `contains(parent, child)` facts for owned
  contained resources and direct `separate(child1, child2)` facts for owned
  sibling resources without exposing the hidden permissions,
- copyable read transfer,
- linear write transfer through function summaries,
- covered subrange splitting and adjacent range rejoining.

Not implemented yet:

- fractional permissions,
- C heap allocation or allocation-sized deallocation semantics,
- deallocation/free authority in the Click resource surface,
- custom resource-family algebra,
- implicit resource unfold/fold search in `auto`,
- persistent token resources,
- ownership predicates,
- explicit resource algebra proof steps,
- general mutable spec/model state.

The current permission layer is intentionally small. It should be treated as the
foundation for broader permission logic, not as the final ownership model.
