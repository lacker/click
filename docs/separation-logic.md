# Separation Logic Internals

This page is an internal design target for Click's resource system. It explains
the separation-logic shape we want the implementation to move toward. It is not
new surface syntax.

Click is not currently implemented as a full Iris-style resource algebra. The
current implementation has a concrete `ResourceContext` containing `CResource`
tokens, with family-specific code for entailment, consumption, splitting, and
joining. The intended direction is to make that code line up with a small,
explicit algebraic model.

## Current Resource Cases

The Click surface currently has memory clauses and named-resource clauses:

```text
read(range)
write(range)
named(name, arguments)
```

The kernel resource state now represents memory clauses through a subject plus
an access mode:

```text
view(memory(range))  // surface read(range)
own(memory(range))   // surface write(range)
named(name, arguments)
```

Composite resources are not a separate kernel resource case. A composite
resource is a named resource with a body in the Click resource environment:

```click
resource owner_buffer(owner: struct owner*) {
    contains write(owner[0..1]);
    contains write(owner->data[0..owner->len]);
    fact owner->len >= 0;
}
```

When `owner_buffer(owner)` is packed, the resource context holds a named token.
Its contained resources stay hidden until `unpack(owner_buffer(owner))`. Its
declared facts, and some facts derived from the contained resources, may be
observed without unpacking.

So the current surface categories are better described as:

- memory read resources,
- memory write resources,
- named resources, some of which are composite resources.

Internally, the memory cases are `View(Memory(...))` and `Own(Memory(...))`.
The kernel stores a packed composite resource as a named token today; the
composite body is consulted by proof-layer `pack`, `unpack`, and `observe`
operations.

## Resource State

The algebraic carrier is `M`: the type of resource-state elements. A value of
type `M` is not the whole C memory state. It is the proof-side claim about which
logical resources are currently held.

At the Click surface, a contract writes separate resource clauses:

```click
requires write(p[0..1]);
requires read(q[0..1]);
requires owner_buffer(owner);
```

Internally, those clauses should be understood as elements composed into one
resource state:

```text
write(p[0..1]) * read(q[0..1]) * owner_buffer(owner)
```

The current implementation represents this as a normalized list of concrete
tokens. The design target is to treat it as an element of `M`.

## Algebraic Operations

The minimal algebraic interface is:

```text
empty   : M
compose : M x M -> M
valid   : M -> Prop
core    : M -> M
```

`empty` is the resource state that holds nothing.

`compose(left, right)` combines two resource claims. Conceptually this operation
is total: it can build a combined element even if the result is incoherent.

`valid(m)` says whether a resource state is coherent. For example, two
exclusive write claims to overlapping memory should compose to an invalid
state:

```text
valid(write(p[0..1]) * write(p[0..1])) = false
```

`core(m)` returns the duplicable read-only view of `m`. For memory resources,
Click wants:

```text
core(view(memory(range))) = view(memory(range))
core(own(memory(range)))  = view(memory(range))
```

That is why a surface `write(...)` resource, internally
`own(memory(...))`, can satisfy a surface `read(...)` requirement, internally
`view(memory(...))`, without losing the write authority.

In the current code, `CResource::core()` returns `Option<CResource>` because a
single strict token may have no non-empty core. `None` means the empty core for
that token. The full resource-state `core` is the composition of the non-empty
cores of the held tokens.

## Total Compose Vs Try Compose

The design model separates `compose` from `valid` because those are different
questions:

- `compose` asks what it means to put two claims together.
- `valid` asks whether the combined claim can actually exist.

The Rust implementation does not have to expose an invalid state everywhere.
For engineering convenience, a resource-family implementation may use a partial
operation such as:

```text
try_compose(left, right) -> Result<M, InvalidReason>
```

That should be treated as `compose` followed by a validity check. The
conceptual model remains useful because it gives a clear answer to questions
like "why do two writes imply disjointness?" They imply it because a valid
composition containing both write authorities rules out overlap.

## Assertions

Click resource clauses are assertions over `M`. Separating conjunction means
that a resource state can be split into independent pieces:

```text
P * Q
```

means there are `m1` and `m2` such that:

```text
P holds over m1
Q holds over m2
valid(compose(m1, m2))
```

This is the separation-logic meaning behind a function requiring several
resources. The function does not receive a bag of unrelated facts. It receives
a coherent resource state whose pieces can be transferred, consumed, observed,
or repackaged according to their algebraic rules.

## Observable Facts

Click also needs a deterministic way to turn held resources into ordinary proof
facts. This is the role currently played by composite-resource fact
projection and `observe(resource)`.

The design target is:

```text
facts : M -> Prop list
```

or, more precisely, each resource family should define which ordinary facts are
observable from a valid held resource state.

Examples:

- A composite resource exposes its declared `fact` clauses while packed.
- A valid state containing two owned memory resources exposes that their ranges
  are disjoint.
- An owned memory resource exposes its viewed memory core, but the viewed core
  is still a resource, not an ordinary proposition.

This distinction matters. `observe(...)` should be a deterministic proof step
that adds ordinary observable facts. It should not unpack hidden permissions,
and it should not mutate the resource state.

In the current code, `ResourceContext::observable_facts(...)` is the beginning
of this interface. It derives ordinary facts from the concrete resource state
after checking resource-state validity. Today it exposes disjointness facts
from valid compositions of multiple owned memory resources. Composite-resource
`fact` clauses are grouped into the same composite-resource observable-facts
projection path. Their lowering still lives in the Click proof layer because it
depends on resource definitions, substitution, and memory materialization.

## Memory Resource Rules

The memory family should satisfy these rules:

- `view(memory(range))`, exposed as `read(range)`, permits loads from `range`.
- `own(memory(range))`, exposed as `write(range)`, permits loads and stores to
  `range`.
- `core(view(memory(range))) = view(memory(range))`.
- `core(own(memory(range))) = view(memory(range))`.
- viewed memory resources are duplicable.
- owned memory resources are exclusive.
- A valid state cannot contain overlapping owned memory ranges.
- Adjacent or covering memory resources may be normalized when facts prove the
  ranges line up.
- A store through owned memory updates the symbolic memory state. Later reads
  see the updated value unless another owner writes a new value.
- Repeated reads with no intervening write to the same cell are stable.

Read stability is a memory-model promise, not a permission to mutate. A
`read(...)` resource allows code to rely on the current cell value across
ordinary repeated loads, but it does not allow stores.

## Named Resource Rules

Plain named resources currently behave as strict linear tokens:

- exact-match entailment only,
- no splitting or joining,
- duplicate identical named tokens are invalid,
- consuming a named resource removes the token,
- returning the same named resource adds the token back.

Composite resources add a definitional layer:

- `unpack(resource)` consumes the packed named token and exposes its contained
  resources.
- `pack(resource)` proves the declared facts, consumes the contained resources,
  and returns the packed named token.
- `observe(resource)` projects observable facts without exposing contained
  resources.

In the algebraic model, a composite resource is not a new primitive kind of
resource. It is a named token with laws connecting the packed token to a
composite body made from other resource assertions and facts.

## Refactor Direction

The current code already has several pieces of this model, but they are
still mostly hardcoded:

- `ResourceContext` is a list of concrete tokens rather than an explicit `M`.
- `ResourceContext::validity_error` is the beginning of an explicit validity
  check, currently covering duplicate named resources and overlapping writes.
- `ResourceContext::try_compose_with_resource(s)(...)` is the beginning of an
  explicit checked composition operation. It validates the raw combined context
  before normalizing it, so invalid combinations cannot merge away before being
  rejected.
- Raw list construction is explicitly named `unchecked_with_resource(s)(...)`.
  It should stay limited to tests and assumption-free lowering/materialization
  paths that build provisional contexts before validity can be checked.
- `CResource::core()` is the beginning of an explicit core operation, currently
  mapping `own(memory(range))` to `view(memory(range))` and strict named tokens
  to empty core.
- Memory and named resources still use separate entailment, consume, and
  combine functions.
- `ResourceContext::observable_facts(...)` is the beginning of an explicit
  observable-facts operation, currently covering owned-memory disjointness.
  Projection paths call it unconditionally so observable-facts projection also
  validates the current resource context.
- Composite-resource observable-facts projection now combines contained
  resource-context observable facts with declared `fact` clauses, but this is
  still implemented in the Click proof layer rather than as a full
  resource-family observable-facts interface.

The next refactor should preserve current behavior while making these concepts
explicit:

1. Introduce names in code and docs that match the model: resource state,
   compose, valid, core, and observable facts.
2. Treat the current memory rules as the first resource-family implementation.
3. Keep composite resources as named resources with composite-body laws.
4. Move hidden disjointness reasoning toward "facts derived from valid
   composition" instead of special cases tied to a particular projection path.
5. Avoid adding new resource features until they can be expressed through this
   interface.

This gives Click an Iris-inspired foundation without requiring the full Iris
machinery in the first implementation.
