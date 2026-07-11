# Permissions

Permissions describe what external memory a proof may access. In the proof
context, permissions are resource facts. They sit alongside pure facts such as
integer bounds, but they obey resource-composition rules because some
permissions must not be copied freely.

Click currently has two first-layer memory permissions:

```click
requires read(p[0..1]);
requires write(p[0..1]);
```

These clauses create resource facts in the verifier's resource context. External C
memory accesses must be covered by the current resource context:

- a load requires `read(...)` or `write(...)`,
- a store requires `write(...)`,
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

The main built-in resource family is memory. `read(...)` and `write(...)` are
memory resource facts over a range. This is similar in spirit to a resource
algebra: the context is not just a bag of pure facts, because each resource
family has rules for combining, transferring, and consuming its facts.

In the first-layer model, `read(...)` is the stable read view of memory.
Algebraically, it is the core of `write(...)`:

```text
core(write(p[lo..hi])) = read(p[lo..hi])
core(read(p[lo..hi])) = read(p[lo..hi])
```

Internally, the kernel now spells this relationship as
`core(own(memory(range))) = view(memory(range))`; the Click surface still uses
`write(...)` and `read(...)`.

That is why a write resource can satisfy read requirements and read guarantees
without consuming the write resource.

This resource-family boundary is intentionally more general than memory
ownership. Click also has exact-match user-defined resources, which can model
API protocols without forcing those protocols to look like heap cells.

## Loadability And Authority

`loadable(...)` and permissions still answer different questions, but access
permissions include the loadability needed for the covered access.

`loadable(p[0..n])` says the range is loadable. It is about
memory safety and bounds.

`read(p[0..n])` or `write(p[0..n])` says the current code has authority to
access that range. It is about permission.

For an external read, `read(...)` is normally enough:

```click
int32 first(int32 p[]) {
    requires read(p[0..1]);

    ensures result == p[0] by auto;
}
```

Similarly, `write(...)` grants authority to store and makes the covered range
loadable. Use `loadable(...)` separately when you need to prove memory exists
without granting read or write authority, or when a larger structural bound is
useful for index reasoning.

When the same loadability fact must appear as a proposition, use
`loadable(segment)`. This is common in composite resource definitions, where
`fact` clauses are pure propositions rather than structural requirements.

## Read Permission

`read(...)` permits loads. It does not permit stores. While no write to the
same cell occurs in the current execution, repeated reads of that cell are
stable: they produce the same symbolic value.

```click
int32 peek(int32 p[]) {
    requires read(p[0..1]);

    ensures read(p[0..1]) by auto;
}
```

Read resources are copyable across function calls. If a caller has
`write(p[0..1])`, it may pass the `read(p[0..1])` core view to a helper and
still keep its write permission afterward.

## Write Permission

`write(...)` permits both loads and stores, so `write(...)` can satisfy an
`ensures read(...)` guarantee. Stores through a write resource update the
symbolic memory state; later reads of the same cell see the written value unless
a later write changes it again.

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

## Token Resources

You can declare an exact-match resource:

```click
resource open_fd(fd: int32);
```

Then a contract can require and return instances of that resource:

```click
int32 borrow_fd(int32 fd) {
    requires open_fd(fd);

    ensures open_fd(fd) by auto;
}
```

A token resource is transferred by function calls. If a callee requires
`open_fd(fd)` and returns it with `ensures open_fd(fd)`, the caller gets the
token back. If the callee requires it and does not return it, the caller loses
the token.

Token resources currently have exact-match behavior only. They do not split,
rejoin, imply other resources, authorize C statements, or define custom algebra
rules. Resource arguments currently support current-state C expressions such as
parameters, constants, arithmetic, pointer expressions, and indexes. Arguments
are checked against the types declared in the resource definition.

Token resources are strict tokens. A resource context cannot contain the
same token resource twice: duplicate clauses such as two
`requires open_fd(fd);` entries are rejected, and a call cannot satisfy two
callee resource parameters with the same token.

A function spec may exist only to consume a resource:

```click
resource can_complete(cb: int32);

int32 complete(int32 cb) {
    requires can_complete(cb);
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
    requires live_fd(fd);

    ensures result >= 0 by {
        observe(live_fd(fd));
        observe(nonnegative_fd(fd));
        symbolic_execute();
        simp();
    }

    ensures live_fd(fd) by auto;
}
```

The first `observe` exposes a viewed `nonnegative_fd(fd)` resource. The second
`observe` exposes that resource's immediate fact, `fd >= 0`. Neither step
consumes `live_fd(fd)`, and neither step unfolds owned permissions.

When code needs the contained owned resources, use `unfold(resource)`. When
the proof has rebuilt the body, use `fold(resource)`:

```click
resource uncalled(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}

resource called(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 1;
}

int32 complete_once(int32 flag[]) {
    requires uncalled(flag);

    ensures called(flag) by {
        unfold(uncalled(flag));
        symbolic_execute();
        fold(called(flag));
    }

    ensures result == 1 by {
        unfold(uncalled(flag));
        symbolic_execute();
        fold(called(flag));
        simp();
    }
}
```

`unfold(uncalled(flag))` consumes the folded `uncalled(flag)` resource and adds
the contained `write(flag[0..1])` resource to the proof state. The C execution
can then mutate the flag. `fold(called(flag))` proves the `called` body's fact,
consumes the contained write resource, and adds the folded `called(flag)`
resource. The end of the `by { ... }` block checks the overall claim.

`fold` also builds a composite resource from lower-level resources at a
function boundary:

```click
int32 init_once(int32 flag[]) {
    requires write(flag[0..1]);

    ensures uncalled(flag) by {
        symbolic_execute();
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

If a fact reads mutable memory, the composite body must contain write
permission covering that memory. This is what makes the fact stable while
the resource is folded:

```click
resource uncalled(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}
```

The coverage check can use scalar facts from the fact itself:

```click
resource indexed_zero(p: int32*, k: int32, n: int32) {
    contains write(p[0..n]);
    fact 0 <= k and k < n and p[k] == 0;
}
```

This symbolic check proves the index is inside the range; the memory base must
still match the contained write resource directly.

`read(flag[0..1])` is not enough for this purpose. A read resource authorizes
inspection but does not prevent another holder of write permission from
changing the cell. Pure scalar facts such as `fd >= 0` do not need a contained
memory resource.

This is resource-context reasoning, not theorem application. Theorems stay
pure; `apply(theorem(...))` can add proposition facts, but it does not consume
or return resources.

This first slice supports built-in `read(...)` and `write(...)` clauses plus
exact-match token resources inside `contains`. Duplicate contained resource
tokens are rejected, and composite-resource cycles are rejected. Resource
unfolding is explicit; `auto` does not yet choose unfold/fold steps on its own.

The smallest ownership-shaped pattern is a composite resource that bundles
several concrete permissions. For example, `first_cell_copy_access(dst, src)`
can contain `write(dst[0..1])` and `read(src[0..1])`, while
`owned_one_cell(owner, data)` can contain permission for an owner object and an
explicitly passed buffer pointer. In this conservative shape, the resource's
parameters name the lower-level memory objects directly. More convenient
field-dependent composite resources can derive a contained buffer from
`owner->data`. The folded resource exposes derived `disjoint(...)` facts from
its hidden contained writes, while explicit `fact` clauses can carry additional
shape facts such as length and capacity. A push-style buffer resource can use a
stronger pre-state resource, such as `owned_buffer_with_room(owner)`, with
facts like `owner->len < owner->cap`; after the mutation, the proof can fold
back to the ordinary `owned_buffer(owner)` shape.

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
- `read(...)` and `write(...)` over memory ranges,
- an internal memory resource family boundary for entailment, consumption,
  access authorization, splitting, and joining,
- exact-match token resources declared with `resource name(...)`,
- composite resources with explicit `unfold(resource)` and
  `fold(resource)` proof steps, including composition over other declared
  resources,
- one-step fact views for folded composite resources, plus
  `observe(resource)` proof steps that explicitly record fact-view projection
  without exposing contained permissions,
- `write(...)` implying read authority,
- visible owned resources imply `separate(...)` facts, with
  `separate(memory(...), memory(...))` implying `disjoint(...)`; provably
  overlapping visible writes are rejected,
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
