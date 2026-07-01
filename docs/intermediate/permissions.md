# Permissions

Permissions describe what external memory a proof may access. They are separate
from ordinary propositions because some permissions must not be copied freely.

Click currently has three memory permissions:

```click
requires read(p[0..1]);
requires write(p[0..1]);
requires free(p[0..1]);
```

These clauses create resources in the verifier's resource context. External C
memory accesses must be covered by the current resource context:

- a load requires `read(...)` or `write(...)`,
- a store requires `write(...)`,
- local stack memory does not require a resource.

## Resource Context And Families

Internally, Click treats permissions as resources. A resource is a proof-side
token carried in the current resource context. A resource family defines the
rules for a group of related resources:

- when one resource entails another,
- whether a resource is copyable or linear,
- how resources split and rejoin,
- what gets consumed by a function call or statement,
- what other resources are invalidated by consumption.

The main built-in resource family is memory resources. `read(...)`,
`write(...)`, and `free(...)` are all memory resources over a range. This is
similar in spirit to a resource algebra: the context is not just a bag of facts,
because each family has rules for combining, transferring, and consuming its
resources.

This resource-family boundary is intentionally more general than memory
ownership. Click also has a first exact-match slice for user-defined affine
resources, which can model API protocols without forcing those protocols to
look like heap cells.

## Validity And Authority

`valid_range(...)` and permissions answer different questions.

`valid_range(p[0..n])` says the range is a valid memory range. It is about
memory safety and bounds.

`read(p[0..n])` or `write(p[0..n])` says the current code has authority to
access that range. It is about permission.

For an external read, you normally need both:

```click
int32 first(int32 p[]) {
    requires valid_range(p[0..1]);
    requires read(p[0..1]);

    ensures result == p[0] by auto;
}
```

For a write, `write(...)` grants authority to store. In the current
implementation, concrete `int32[]` write ranges also seed the symbolic memory
cells for that range, so small write examples often do not need a separate
`valid_range(...)` clause. This is an implementation convenience, not the
general ownership model.

## Read Permission

`read(...)` permits loads. It does not permit stores.

```click
int32 peek(int32 p[]) {
    requires valid_range(p[0..1]);
    requires read(p[0..1]);

    ensures read(p[0..1]) by auto;
}
```

Read resources are copyable across function calls. If a caller has
`write(p[0..1])`, it may pass `read(p[0..1])` to a helper and still keep its
write permission afterward.

## Write Permission

`write(...)` permits both loads and stores, so `write(...)` can satisfy an
`ensures read(...)` guarantee.

```click
int32 set_one(int32 p[]) {
    requires write(p[0..1]);

    ensures write(p[0..1]) by auto;
}
```

Write resources are linear across function calls. A callee only receives write
permission if its contract declares `requires write(...)`. The caller loses
that write resource for the duration of the call. If the callee does not return
it with `ensures write(...)`, the caller cannot use or prove it afterward.

This is the main difference between a permission and an ordinary proposition.
Ordinary facts can be used repeatedly. A write resource can be transferred.

## Free Permission

`free(...)` represents authority to release a range. It is separate from access
permission:

- `free(...)` does not permit loads,
- `free(...)` does not permit stores,
- `write(...)` does not imply `free(...)`.

This lets a contract say that code may write a field without being allowed to
release the whole object.

Free resources are linear. If a callee requires
`free(p[0..1])` and does not return it, the caller loses that free resource.
Consuming a free resource also removes overlapping `read(...)` and `write(...)`
resources from the caller context. That models the permission consequence of
deallocation: after handing off authority to release a range, the caller cannot
continue accessing that same range unless the callee explicitly returns the
needed resources.

The executable C0 statement `free(p);` consumes `free(p[0..1])` and removes
overlapping access resources in the same way. This is still a narrow
resource-level model: Click does not yet have C heap allocation, allocation-size
tracking, or block invalidation.

## Function Calls

Function calls use the callee's resource summary:

```click
int32 helper(int32 p[]) {
    requires write(p[0..1]);
    ensures write(p[0..1]) by auto;
}

int32 caller(int32 p[]) {
    requires write(p[0..1]);
    ensures write(p[0..1]) by auto;
}
```

The caller must have a resource that covers every callee resource requirement.
An unannotated callee receives no external memory permission, even if the caller
has permissions in its own context.

## Affine Named Resources

You can declare an exact-match affine resource:

```click
affine resource open_fd(fd: int32);
```

Then a contract can require and return instances of that resource:

```click
int32 borrow_fd(int32 fd) {
    requires open_fd(fd);

    ensures open_fd(fd) by auto;
}
```

An affine named resource is transferred by function calls. If a callee requires
`open_fd(fd)` and returns it with `ensures open_fd(fd)`, the caller gets the
token back. If the callee requires it and does not return it, the caller loses
the token.

Named resources currently have exact-match behavior only. They do not split,
rejoin, imply other resources, authorize C statements, or define custom algebra
rules. Resource arguments currently support current-state C expressions such as
parameters, constants, arithmetic, pointer expressions, and indexes. Arguments
are checked against the types declared in the resource definition.

Affine named resources are strict tokens. A resource context cannot contain the
same named affine resource twice: duplicate clauses such as two
`requires open_fd(fd);` entries are rejected, and a call cannot satisfy two
callee resource parameters with the same token.

A function spec may exist only to consume a resource:

```click
affine resource can_complete(cb: int32);

int32 complete(int32 cb) {
    requires can_complete(cb);
}
```

That spec contributes a call summary. Calling `complete(cb)` consumes
`can_complete(cb)`, so a second call on the same path fails unless some other
contract returns the resource.

## Split And Rejoin

A caller can pass a subrange of a larger write resource:

```click
int32 helper(int32 p[]) {
    requires write(p[0..1]);
    ensures write(p[0..1]) by auto;
}

int32 caller(int32 p[]) {
    requires write(p[0..2]);
    ensures write(p[0..2]) by auto;
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
- `read(...)`, `write(...)`, and `free(...)` over memory ranges,
- an internal memory resource family boundary for entailment, consumption,
  access authorization, splitting, and joining,
- exact-match affine named resources declared with `affine resource name(...)`,
- `write(...)` implying read authority,
- copyable read transfer,
- linear write transfer through function summaries,
- linear free transfer that removes overlapping access resources when consumed,
- executable `free(p);` as a one-cell free-resource consumer,
- covered subrange splitting and adjacent range rejoining.

Not implemented yet:

- fractional permissions,
- C heap allocation or allocation-sized deallocation semantics,
- custom resource-family algebra,
- persistent named resources,
- ownership predicates,
- explicit resource algebra proof steps,
- general mutable spec/model state.

The current permission layer is intentionally small. It should be treated as the
foundation for broader permission logic, not as the final ownership model.
