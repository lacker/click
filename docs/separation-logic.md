# Separation Logic Internals

This page describes Click's internal resource architecture. The algebraic
notation is explanatory; function contracts use the resource verbs described
in the language guide.

Click is not a full Iris implementation. It has a concrete `ResourceContext`
containing `CResourceFact` values and a `ResourceFamilyAlgebra` interface that
defines validity, entailment, consumption, normalization, core, and observable
facts for each built-in family.

## Current Resource Cases

The Click surface has memory resources and declared resources:

```text
memory(range)
name(arguments)
```

The kernel distinguishes resources from resource facts. A resource is the bare
thing being described, such as `memory(range)` or
`composite(name, arguments)`. A resource fact is the thing held in the proof
context: a resource plus an access mode. Internally, the Rust type for a
resource fact is currently `CResourceFact`.

```text
view(memory(range))
own(memory(range))
view(token(name, arguments))
own(token(name, arguments))
view(composite(name, arguments))
own(composite(name, arguments))
```

Bodyless declarations are token resources. Declarations with a body are
composite resources:

```click
resource owner_buffer(owner: struct owner*) {
    owns owner[0..1];
    owns owner->data[0..owner->len];
    fact owner->len >= 0;
}
```

When `owner_buffer(owner)` is folded, the resource context holds an owned
composite resource fact. Its contained resource facts stay hidden until
`unfold(owner_buffer(owner))`. Its declared pure facts, and some pure facts
derived from the contained resource facts, may be observed without unfolding.

Surface verbs lower to these resource facts:

- `views range` lowers to `view(memory(range))`,
- `owns range`, `consumes range`, and `produces range` use
  `own(memory(range))`,
- the same verbs select owned or viewed elements for token and composite
  resources.

The access modes are `own` and `view`. The composite body is consulted by
proof-layer `fold`, `unfold`, and `observe` operations.

## Resource State

The algebraic carrier is `M`: the type of resource states. A value of type `M`
is not the whole C memory state. It is the proof-side state formed by composing
resource facts.

At the Click surface, a contract writes separate resource clauses:

```click
consumes p[0..1];
views q[0..1];
consumes owner_buffer(owner);
```

Internally, those clauses should be understood as resource facts composed
into one resource state:

```text
own(memory(p[0..1])) * view(memory(q[0..1])) * own(owner_buffer(owner))
```

The implementation represents this as a normalized list of concrete resource
facts. Algebraically, the whole list is one resource state in `M`.

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
valid(own(memory(p[0..1])) * own(memory(p[0..1]))) = false
```

`core(m)` returns the duplicable read-only view of `m`. For memory resources,
Click wants:

```text
core(view(memory(range))) = view(memory(range))
core(own(memory(range)))  = view(memory(range))
```

That is why `owns p[...]` can satisfy a callee's `views p[...]` requirement
without losing write authority.

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
like "why do two writes imply non-overlap?" They imply it because a valid
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

The internal proof-script model is a state transformer over:

```text
goal
pure facts
symbolic C state
resource facts
execution frontier
```

The execution frontier contains the point where symbolic execution is paused
and the continuation stack for enclosing branch regions. The current
implementation has these frontier points:

- function entry, before C execution has started,
- statement entry after `execute_step()`, explicit entry into a selected `if`
  arm, or a straight-line `execute_until(statement(N))` pause,
- function exit, after `execute_rest()` / `symbolic_execute()` has executed the
rest of the function.

Condition edges and statement execution produce shared certified transitions.
The ordinary execution tactics and region execution-proof traversal consume
those same transitions, so they cannot disagree about successor states, generated
facts, or missing prerequisites. Whether the frontier is inside a branch is
derived from its continuation stack rather than maintained as an independent
flag.

The loop preservation execution proof packages its abstract exit transitions as an
opaque kernel `VerifiedLoopRule`. The symbolic values in its entry state stand
for arbitrary values constrained by the rule's required assumptions. Later
execution may strengthen those assumptions, but it must apply the registered
rule when crossing an annotated loop. A missing or incompatible rule is a
proof failure, not a request to run automatic loop verification again.

Each loop-rule premise can be automatic or explicit. Explicit `initialize` is a
pure proof of the invariants at the actual loop entry. Explicit `preserve` is an
execution proof that advances through one arbitrary iteration and checks every
reached back edge. These proofs feed the abstract-exit constructor directly;
the kernel does not prove either supplied premise again. An omitted phase uses
automatic verification for that premise.

`apply(...)` and `have ... by { ... }` perform pure proofs at the current
execution point. `observe(...)`, resource `unfold(...)`, and `fold(...)` perform
resource reasoning there. None advances execution. This lets deterministic
proof steps prepare facts and resources before the next C statement. At function exit, operations
whose meaning depends on `result` or the post-state are checked separately for
each completed execution path.

`execute_step()` is the primitive execution proof step. It advances by one
supported straight-line statement and expects needed pure facts and resource
facts to already be available in the proof context.

`advance(point) ensuring { Q } by { steps }` is the sequencing rule for scoped
execution. Every proof case in `steps` must reach `point` and prove `Q`. Click
then replaces branch-local scalar values, mutable memory, pure facts, resource
facts, and snapshots with one fresh symbolic frontier satisfying exactly `Q`
and its deterministic resource consequences. The continuation therefore cannot
depend on an unstated branch fact. Stable function parameters and the function
entry state used by `old(...)` retain their identity across the boundary.

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

The deterministic interface is:

```text
observe : resource fact -> pure facts + resource facts
```

or, more precisely, each resource family defines which pure facts and
resource facts are observable from a valid held resource state.

Examples:

- A composite resource exposes its declared pure `fact` clauses while folded.
- A declared `fact loadable(data[0..cap])` exposes a pure memory-loadability fact
  for the segment without exposing the contained resource fact that justified it.
- A valid state containing two owned memory resources exposes that their ranges
  are separate.
- An owned memory resource exposes its viewed memory core, but the viewed core
  is a resource fact, not a pure fact.

This distinction matters. `observe(...)` should be a deterministic proof step
that adds observable pure facts and viewed immediate contained resource facts.
It should not unfold hidden owned permissions, and it should not consume the
observed resource fact. It should also stay one-step: recursive expansion of
large composite resources belongs behind an explicit bounded proof step or
future summary mechanism, not in default `auto` behavior.

`ResourceContext::observable_facts(...)` implements the pure-fact side of this
interface. It validates the concrete resource state, asks each family for its
observations, and adds separation between owned facts from different families.
Composite-resource `fact` clauses join the same observable-pure-facts projection
path. Their lowering lives in the Click proof layer because it depends on
resource definitions, substitution, and memory materialization.

## Memory Separation

Click does not expose a separate memory-specific non-overlap predicate. Memory
non-overlap is stated through the general resource-separation proposition:

The more general idea is valid composition of resource facts:

```text
valid(compose(own(memory(range1)), own(memory(range2))))
```

```click
separate(memory(range1), memory(range2))
```

`separate(r1, r2)` means the owned versions of `r1` and `r2` can coexist in the
resource algebra. For owned memory facts, that valid composition rules out
overlap between the memory ranges.

Click also exposes resource inclusion/decomposition as:

```click
contains(parent, child)
```

`contains(parent, child)` means owning `parent` can provide `child` plus some
remaining resource. This is algebraic containment, not necessarily physical
field containment. For example, a future arena resource could contain a smaller
amount of arena space even when that space is interchangeable.

Composite resources project direct `contains(parent, child)` facts for owned
contained resources and direct `separate(child1, child2)` facts for owned
sibling resources. Deeper facts come from deterministic theorem steps:
`contains` is transitive, `separate` projects through contained children, and
memory `separate` implies memory non-overlap for frame reasoning.

## Memory Resource Rules

The memory family implements these rules:

- `view(memory(range))`, requested with `views range`, permits loads from
  `range`.
- `own(memory(range))`, requested with `owns`, `consumes`, or `produces`,
  permits loads and stores to `range`.
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

Read stability is a memory-model promise, not a permission to mutate. A viewed
memory resource allows code to rely on the current cell value across ordinary
repeated loads, but it does not allow stores.

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

## Implementation Boundary

The code maps onto this model as follows:

- `ResourceContext` is the concrete representation of a resource state `M`.
- `try_compose_with_fact(s)` appends facts, checks validity before
  normalization, and then applies family normalization rules.
- `ResourceFamilyAlgebra` is the internal family contract. It supplies
  same-family validity, entailment, consumption and residual ownership,
  pair normalization, core, and observable facts.
- `MemoryResourceAlgebra` implements range coverage, splitting, joining,
  exclusive writes, and viewed cores.
- `TokenResourceAlgebra` implements strict exact-match tokens.
- `CompositeResourceAlgebra` implements the folded fact's exact-match algebra.
  Source declarations add separate definition laws connecting that folded fact
  to its body.
- `ResourceContext::observable_facts` combines family observations with the
  generic theorem that distinct owned facts in a valid composition are
  separate.
- Raw `unchecked_with_fact(s)` construction is limited to tests and
  assumption-free materialization paths that produce provisional states.

Composite definition laws remain in the Click proof layer because they require
source-level argument substitution, proposition lowering, and symbolic-memory
materialization. `observe`, `unfold`, and `fold` are the explicit operations
that apply those laws.

New primitive resource families should implement this interface rather than add
dispatch to `ResourceContext`. Features such as fractional ownership,
authoritative ghost state, allocation authority, and invariants are not yet
implemented.
