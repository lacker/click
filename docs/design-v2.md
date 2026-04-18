# Click Design V2

This document sketches an exploratory redesign of Click.

The main shift is:

- V1 treats Click as a typed proof-oriented kernel with reflection added later.
- V2 treats Click as a reflective computation core first, with typing and proof
  checking layered on top.

The goal is a smaller and more uniform computational substrate, one that is
powerful enough to express its own evaluator inside Click without making typed
proof theory the first trusted abstraction.

## Goal

Click V2 should be:

- small enough to understand operationally
- uniform enough that code and data use the same raw representation
- expressive enough to define `eval` inside Click
- permissive enough to represent possibly diverging programs
- open to Curry-style typing and proof checking as ordinary programs above the
  core

The core should be a kernel that computes. Proof checking comes later.

## Raw Terms

A raw Click `Term` is one of two things:

- `Symbol`
- `Object`

A `Symbol` is an atomic value such as `:foo`.

An `Object` is a finite unordered map from unique symbol keys to term values.

So the entire raw language is:

```text
Term ::= Symbol | Object(Symbol -> Term)
```

There are no builtin lists, builtin sum types, or builtin product types at the
raw level. Those are all conventions layered on top of `Object`.

Types are not primitive terms in the core. V2 aims at a Curry-style story where
typing is a later judgment over raw terms, not part of the trusted syntax.

## Surface Notation

The exact surface syntax is still open.

This document uses two pieces of notation:

- bare symbols like `:x`
- object literals written in a readable object style

For example:

```text
{ :left value }
{ :x a, :y b }
```

This notation is schematic. The actual parser may use a different concrete
syntax. The important part is the semantic shape:

- symbol literals are data
- object literals are data

The core evaluator gives special meaning to certain distinguished symbols when
they appear in specific object shapes, but there is no separate trusted term
datatype for functions, applications, matches, or types.

## Data Model

The raw `Object` substrate is intended to play multiple roles.

Products can be represented directly as objects with several fields:

```text
{ :x a, :y b }
```

Sum-like values can be represented as singleton-key objects:

```text
{ :left payload }
{ :right payload }
```

Environments are objects:

```text
{ :x value, :y value2 }
```

Closures are objects.

Syntax trees are objects.

Proof terms and proof checkers can also be objects.

This is the main conceptual attraction of V2: one raw representation is reused
everywhere.

## Values

The simplest value discipline is:

- every `Symbol` is a value
- every literal `Object` is a value

There is no automatic evaluation underneath literal objects.

So:

```text
{ :x (:apply f a) }
```

is data, not an eager computation. This is important for reflection. If Click
is going to represent its own code and evaluator, raw object structure should
be inert by default.

Computed object construction therefore needs explicit computational forms such
as `:set`, rather than relying on evaluation inside object literals.

## Computational Forms

V2 still needs some computational meaning. The current working hypothesis is
that a small set of distinguished symbols will name primitive executable forms.

The first candidate set is:

- `:var`
- `:lambda`
- `:apply`
- `:match`
- `:set`

There may later be more, but this is the minimal set currently under
consideration.

### Concrete Encodings

The current concrete encoding proposal is:

```text
(:var :x)
== { :var :x }

(:lambda :x body)
== { :lambda { :param :x, :body body } }

(:apply f x)
== { :apply { :function f, :arg x } }

(:match handlers value)
== { :match { :handlers handlers, :value value } }

(:set object key value)
== { :set { :object object, :key key, :value value } }
```

These are singleton-key objects whose payload is either a symbol or another
object.

Any object that does not match one of these executable shapes is ordinary data.

### `:var`

Variable lookup should be explicit.

Bare symbols are data:

```text
:x
```

Variable references are expressions:

```text
(:var :x)
```

This keeps symbols usable as ordinary data while still allowing lexical scope.

### `:lambda`

A lambda form introduces one symbol name and one body:

```text
(:lambda :x body)
```

Operationally `:lambda` should evaluate to a closure.

### `:apply`

Function application should be explicit:

```text
(:apply f x)
```

The language is meant to feel lambda-calculus-ish, so `:apply` is preferred to
`:call`.

### `:match`

`match` is intended to be the generic eliminator for raw terms, especially
objects. The current design instinct is "sloppy" matching by overlapping keys.

If:

```text
handlers = { :k1 h1, :k2 h2 }
value    = { :k2 payload }
```

then:

```text
(:match handlers value)
```

should dispatch to:

```text
(:apply h2 payload)
```

The first version should probably require exactly one overlap between handler
keys and value keys. Otherwise `step` should return an error.

This lets singleton-key objects play the role of tagged sum values, while
handler objects play the role of eliminators.

Because literal objects are inert data, `match` should evaluate the selected
handler explicitly before applying it. A handler object can therefore contain
raw `:lambda` forms without forcing evaluation of every field up front.

`match` may eventually subsume older primitives like:

- `get`
- `has`
- `if`

but the exact pattern story is still open.

### `:set`

Because literal objects are inert data, the core likely needs a way to build or
update objects computationally:

```text
(:set object key value)
```

`set` is not the fundamental way objects exist. Literal objects already exist.
`set` is for computed updates and explicit object construction inside programs.

## Environments and Closures

V2 probably wants lexical scope through explicit environments rather than
substitution-heavy evaluation.

The current intended split is:

- `(:lambda :x body)` evaluates to a closure object
- a closure captures its defining environment
- `:apply` on a closure extends that environment with `:x -> arg`
- the body is then evaluated in the extended environment

The first concrete closure shape is:

```text
{ :closure { :param :x, :body body, :env env } }
```

Closures should be ordinary objects so that they remain reflectable like
everything else.

## Machine State

Unlike V1, V2 should make error and control-state propagation explicit.

`step` should operate on a state-like term and return a small sum-like object:

```text
{ :continue next }
{ :return value }
{ :error info }
```

This means:

- `:continue` says another step is needed
- `:return` says evaluation has produced a value
- `:error` says something invalid happened

The "sum type" here is not primitive. It is just the singleton-object idiom.

The input to `step` should be an explicit evaluator state.

The first concrete state shapes are:

```text
{ :eval { :expr expr, :env env, :cont cont } }
{ :ret  { :value value, :cont cont } }
```

The first concrete continuation shapes are:

```text
:halt

{ :apply_function { :arg arg, :env env, :next cont } }
{ :apply_argument { :function function_value, :next cont } }

{ :set_object { :key key, :value value, :env env, :next cont } }
{ :set_key { :object object_value, :value value, :env env, :next cont } }
{ :set_value { :object object_value, :key key_value, :next cont } }

{ :match_handlers { :value value_expr, :env env, :next cont } }
{ :match_value { :handlers handlers_value, :env env, :next cont } }
{ :match_apply { :payload payload, :next cont } }
```

This keeps environments and control flow explicit and avoids relying on
host-side hidden state.

## Errors

V2 should support errors directly in the step protocol.

If anything operationally weird happens, `step` should return `:error` instead
of forcing the host to panic or invent side channels.

Examples:

- applying a non-closure
- looking up an unbound variable
- matching with zero overlapping keys
- matching with more than one overlapping key, if exact-single-overlap is the
  chosen rule
- malformed executable object shapes

This keeps the kernel operationally honest.

## Evaluation Strategy

The intended strategy is small-step and explicit.

One step should do local work. In particular:

- step should not recursively walk whole source trees in Rust
- step should inspect one explicit evaluator state
- step may build one new state or value
- step may perform closure application and environment extension
- substitution, if it exists at all, should not be the main runtime model

The long-term goal is that Click can express its own evaluator in terms of this
same state-passing core.

## Typing and Proofs

Typing is not part of the trusted raw syntax in V2.

The intended Curry-style direction is:

- raw terms exist before typing
- a type is a later recognizer, predicate, or checker over raw terms
- proof checking is another program layered on top of raw computation

So V2 is not trying to make every raw term fundamentally carry a type.

This is deliberate. The motivation for V2 is exactly the sense that a
proof-kernel-first architecture fits badly with a reflective language that
should represent and type-check possibly diverging programs before knowing
whether they terminate.

## What V2 Buys

If this works, it gives Click:

- a simpler reflective core
- code and data with the same raw representation
- first-class environments and closures as ordinary objects
- a better story for representing partial or diverging programs
- a path toward self-hosted `eval`
- proof checking as a layer rather than a burden on the base calculus

## Main Open Questions

V2 is still only a sketch. The important open questions are:

- Should object matching require exactly one overlap, or allow more structure?
- How should `:match` handle symbols?
- Is `:set` enough for computed object construction, or is another helper
  needed?
- Should there be a default-match convention, or should all ambiguity be an
  error?
- How much of evaluation should be phrased through explicit state objects, and
  how much should be left to host-side convenience wrappers?

## Next Steps

The next useful experiments are:

1. Implement a tiny Rust evaluator for the V2 state machine in a separate
   `v2`-specific module or crate.
2. Express a first self-interpreter sketch inside Click terms.
3. Only after that, revisit what a typing or proof-checking layer should look
   like above V2.
