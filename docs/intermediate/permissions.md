# Permissions

Permissions describe what external memory a proof may access. They are separate
from ordinary propositions because some permissions must not be copied freely.

Click currently has two memory permissions:

```click
requires read(p[0..1]);
requires write(p[0..1]);
```

These clauses create resources in the verifier's resource context. External C
memory accesses must be covered by the current resource context:

- a load requires `read(...)` or `write(...)`,
- a store requires `write(...)`,
- local stack memory does not require a resource.

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
- `read(...)` and `write(...)` over `int32[]` and `uint8[]`,
- `write(...)` implying read authority,
- copyable read transfer,
- linear write transfer through function summaries,
- covered subrange splitting and adjacent range rejoining.

Not implemented yet:

- fractional permissions,
- allocation or `free` permissions,
- abstract resource predicates,
- ownership predicates,
- explicit resource algebra proof steps,
- general mutable spec/model state.

The current permission layer is intentionally small. It should be treated as the
foundation for broader permission logic, not as the final ownership model.
