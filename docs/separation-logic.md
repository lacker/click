# Separation Logic Internals

This page is an internal design target for Click's resource system. It explains
the separation-logic shape we want the implementation to move toward. It is not
new surface syntax.

Click is not currently implemented as a full Iris-style resource algebra. The
current implementation has a concrete `ResourceContext` containing
`CResourceFact` values, with family-specific code for entailment,
consumption, splitting, and joining. The intended direction is to make that
code line up with a small, explicit algebraic model.

## Current Resource Cases

The Click surface currently has memory clauses and declared-resource clauses:

```text
read(range)
write(range)
name(arguments)
```

The kernel distinguishes resources from resource facts. A resource is the bare
thing being described, such as `memory(range)` or
`composite(name, arguments)`. A resource fact is the thing held in the proof
context: a resource plus an access mode. Internally, the Rust type for a
resource fact is currently `CResourceFact`.

```text
view(memory(range))  // surface read(range)
own(memory(range))   // surface write(range)
view(token(name, arguments))
own(token(name, arguments))
view(composite(name, arguments))
own(composite(name, arguments))
```

Bodyless declarations are token resources. Declarations with a body are
composite resources:

```click
resource owner_buffer(owner: struct owner*) {
    contains write(owner[0..1]);
    contains write(owner->data[0..owner->len]);
    fact owner->len >= 0;
}
```

When `owner_buffer(owner)` is folded, the resource context holds an owned
composite resource fact. Its contained resource facts stay hidden until
`unfold(owner_buffer(owner))`. Its declared pure facts, and some pure facts
derived from the contained resource facts, may be observed without unfolding.

So the current surface clauses lower to these resource facts:

- `read(range)` lowers to `view(memory(range))`,
- `write(range)` lowers to `own(memory(range))`,
- a bodyless declared resource lowers to `own(token(name, arguments))` by
  default, or `view(token(name, arguments))` when explicitly viewed,
- a body-backed declared resource lowers to `own(composite(name, arguments))`
  by default, or `view(composite(name, arguments))` when explicitly viewed.

The access modes are `own` and `view`. The composite body is consulted by
proof-layer `fold`, `unfold`, and `observe` operations.

## Resource State

The algebraic carrier is `M`: the type of resource states. A value of type `M`
is not the whole C memory state. It is the proof-side state formed by composing
resource facts.

At the Click surface, a contract writes separate resource clauses:

```click
requires write(p[0..1]);
requires read(q[0..1]);
requires owner_buffer(owner);
```

Internally, those clauses should be understood as resource facts composed
into one resource state:

```text
write(p[0..1]) * read(q[0..1]) * owner_buffer(owner)
```

The current implementation represents this as a normalized list of concrete
resource facts. The design target is to treat the whole list as one resource
state in `M`.

## Algebraic Operations

The minimal algebraic interface is:

```text
empty   : M
compose : M x M -> M
valid   : M -> Prop
core    : M -> M
```

`empty` is the resource state that holds nothing.

`compose(left, right)` combines two resource states. Conceptually this operation
is total: it can build a combined resource state even if the result is
incoherent.

`valid(m)` says whether a resource state is coherent. For example, two
exclusive owned memory resource facts over overlapping ranges should compose to
an invalid state:

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

In the current code, `CResourceFact::core()` returns
`Option<CResourceFact>`, but every current resource fact has a non-empty
viewed core. The full resource-state `core` is the composition of the viewed
cores of the held resource facts.

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

## Proof Script State

The internal proof-script model should be a state transformer over:

```text
goal
pure facts
symbolic C state
resource facts
execution point
```

The execution point is where symbolic execution is currently paused. The
current implementation has these execution-point states:

- function entry, before C execution has started,
- statement entry after `execute_step()` or a straight-line
  `execute_until(statement(N))` pause,
- function exit, after `execute_rest()` / `symbolic_execute()` has executed the
  rest of the function.

That is why `observe(...)` and `unfold(...)` can run before execution reaches
function exit, while `fold(...)`, `apply(...)`, and `simp()` still run after
function-exit execution. This is a transitional shape. The intended direction
is for future proof steps to advance between more execution points and
control-flow joins, so resource steps can happen between C regions.

`execute_step()` is the primitive execution proof step. It advances by one
supported straight-line statement and expects needed pure facts and resource
facts to already be available in the proof context.

Function entry projects `views composite(...)` resources one step
automatically: the view remains available, and immediate contained resource
facts are available through their views. This is entry setup, not a general
recursive execution heuristic.

`symbolic_execute()` is now best understood as legacy spelling for
`execute_rest()`: advance the current execution point to function exit.

## Observable Facts

Click also needs a deterministic way to turn held resource facts into
observable proof facts. This is the role currently played by composite-resource
fact projection and `observe(resource)`.

The design target is:

```text
observe : resource fact -> pure facts + resource facts
```

or, more precisely, each resource family should define which pure facts and
resource facts are observable from a valid held resource state.

Examples:

- A composite resource exposes its declared pure `fact` clauses while folded.
- A declared `fact loadable(data[0..cap])` exposes a pure memory-loadability fact
  for the segment without exposing the contained resource fact that justified it.
- A valid state containing two owned memory resources exposes that their ranges
  are disjoint.
- An owned memory resource exposes its viewed memory core, but the viewed core
  is a resource fact, not a pure fact.

This distinction matters. `observe(...)` should be a deterministic proof step
that adds observable pure facts and viewed immediate contained resource facts.
It should not unfold hidden owned permissions, and it should not consume the
observed resource fact.

In the current code, `ResourceContext::observable_facts(...)` is the beginning
of the pure-fact side of this interface. It derives pure facts from the
concrete resource state after checking resource-state validity. Today it exposes disjointness facts
from valid compositions of multiple owned memory resources. Composite-resource
`fact` clauses are grouped into the same composite-resource observable-pure-facts
projection path. Their lowering still lives in the Click proof layer because it
depends on resource definitions, substitution, and memory materialization.

## Disjointness And Separation

`disjoint(range1, range2)` is a memory-specific proposition. It should not be
treated as the general primitive for separation logic.

The more general idea is valid composition of resource facts:

```text
valid(compose(own(memory(range1)), own(memory(range2))))
```

For owned memory facts, that valid composition has a useful observable
consequence:

```text
disjoint(range1, range2)
```

Other resource families may expose different observable facts from valid
composition, or none at all. Composite resources may expose declared `fact`
clauses and facts derived from their immediate contained resource facts.

Click does not yet have a general user-visible predicate like
`separate(element1, element2)`. Keep `disjoint(...)` as the concrete range
fact, and treat it as one output of the broader resource-fact validity and
observable-facts machinery.

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

## Token And Composite Rules

Plain token resources currently behave as strict linear tokens:

- exact-match entailment only,
- no splitting or joining,
- duplicate identical owned token resources are invalid,
- consuming a token resource removes the token,
- returning the same token resource adds the token back.

Composite resources add a definitional layer:

- `unfold(resource)` consumes one owned composite resource fact and exposes its
  immediate body resource facts and pure facts.
- `fold(resource)` proves the declared pure facts, consumes one immediate body,
  and returns the owned composite resource fact.
- `observe(resource)` projects one view step without consuming the resource
  fact. It exposes immediate pure facts and viewed immediate contained resource
  facts, but not owned contained permissions.

In the algebraic model, a composite resource is not a new primitive resource
family. It is a declared resource whose resource facts have laws connecting the
owned composite resource fact to a composite body made from other resource facts
and pure facts. Its core is the viewed composite resource fact.

## Refactor Direction

The current code already has several pieces of this model, but they are
still mostly hardcoded:

- `ResourceContext` is a list of concrete resource facts, represented as
  `CResourceFact` values, rather than an
  explicit `M`.
- `ResourceContext::validity_error` is the beginning of an explicit validity
  check, currently covering duplicate token resources and overlapping writes.
- `ResourceContext::try_compose_with_fact(s)(...)` is the beginning of an
  explicit checked composition operation. It validates the raw combined context
  before normalizing it, so invalid combinations cannot merge away before being
  rejected.
- Raw list construction is explicitly named `unchecked_with_fact(s)(...)`.
  It should stay limited to tests and assumption-free lowering/materialization
  paths that build provisional contexts before validity can be checked.
- `CResourceFact::core()` is the beginning of an explicit core operation,
  currently mapping `own(resource)` and `view(resource)` to `view(resource)`.
- Memory, token, and composite resources still use family-specific entailment,
  consume, and combine functions.
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
3. Keep composite resources as declared resources with composite-body laws.
4. Move hidden disjointness reasoning toward "facts derived from valid
   composition" instead of special cases tied to a particular projection path.
5. Avoid adding new resource features until they can be expressed through this
   interface.

This gives Click an Iris-inspired foundation without requiring the full Iris
machinery in the first implementation.
