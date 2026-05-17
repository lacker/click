# Click Design

The goal of Click is to make it easy to prove things about programs, no matter
what language those programs are written in.

The Click kernel should therefore be reflectively complete: Click should be able
to represent programs, computations, types, proofs, evaluators, and checkers as
Click data and computations, and should be able to check meaningful proofs about
those mechanisms.

## The Click Type System

Many proof systems are built around dependent types. In the broad sense, Click
should support dependent types: useful program properties often depend on
program values. But Click should not be built around the narrower
proofs-as-types style of dependent type system used by systems like Lean and
Agda, where typechecking is fundamentally tied to deterministic normalization
of total terms.

That style is a poor fit for Click's goal. Practical programs are often
mutable, partial, asynchronous, panic-capable, weakly typed, or written in
languages whose type systems were not designed for theorem proving. Click
should make the prover fit those programs, rather than requiring programs to be
reshaped until they look natural to the prover.

Click's type system should therefore be based on refinement types and subtypes.
At the kernel level, there should be one connected subtype graph with a top type
for all program objects. Every more precise type is a subtype or refinement of
that top type. The main work of the proof system is to establish subtype
relationships: that an existing program, value, computation, or runtime state
belongs to a more precise type than the one it started with.

This means proofs are not expected to live inside the source-language type
itself. A program may arrive with a precise type, a weak type, a union type, or
no useful type at all. Click's job is to attach stronger meaning by proving
refinement and subtype facts about the program as it exists.

Language-specific runtime models will still be necessary. But Click should not
make each language a separate proof universe with its own unrelated notions of
function, computation, type, and evaluation. Foreign programs should be brought
as close as possible to Click's native computation, state, subtype, and proof
machinery, so proofs talk about the original program rather than an opaque
interpreter wrapped around it.

## Raw Terms

A raw Click `Term` is one of two things:

- `Symbol`
- `Object`

A `Symbol` is an atomic value such as `:foo`.

An `Object` is a finite unordered map from unique symbol keys to term values.

So the core data model is:

```text
Term ::= Symbol | Object(Symbol -> Term)
```

There are no primitive lists, products, sums, closures, or types at the raw
level. Those are all conventions or later layers built on top of symbols and
objects.

## Surface Syntax

The current parser is intentionally small and Lispy:

```text
:foo
(:left :payload)
(:x :a :y (:z :b))
```

Bare symbols parse as symbols. Parenthesized forms parse as objects containing
alternating key/value pairs. So:

```text
(:x :a :y (:z :b))
```

parses to the object:

```text
{ :x :a, :y { :z :b } }
```

This is raw data by default. Objects do not evaluate underneath their fields
unless they match one of the distinguished executable shapes described below.

## Executable Shapes

The current reflective core gives special meaning to a small set of singleton
objects:

- `(:var :x)`
- `(:lambda (:param :x :body body))`
- `(:apply (:function f :arg x))`
- `(:match (:handlers handlers :value value))`
- `(:set (:object object :key key :value value))`

Any object that does not match one of those shapes is inert data.

### `:var`

Symbols are data. Variable lookup is explicit:

```text
:x
(:var :x)
```

The first is a symbol value. The second is an expression that reads from the
current environment.

### `:lambda`

Functions are written as objects and evaluate to closure objects. A closure
captures its defining environment.

Concrete closure values use the ordinary object substrate:

```text
{ :closure { :param :x, :body body, :env env } }
```

### `:apply`

Application is explicit:

```text
(:apply (:function f :arg x))
```

Applying a closure extends the closure's environment with its parameter binding
and then evaluates the body in that extended environment.

### `:match`

`match` is the current generic eliminator for object-shaped data.

If:

```text
handlers = { :left h1, :right h2 }
value    = { :left payload }
```

then:

```text
(:match (:handlers handlers :value value))
```

evaluates the selected handler and applies it to `payload`.

The current rule requires exactly one overlapping key between the handler object
and the value object. Zero overlaps and multiple overlaps are both runtime
errors.

### `:set`

Literal objects already exist as raw data. `:set` is the explicit way to build
or update objects with computed keys or values:

```text
(:set (:object object :key key :value value))
```

## Environments And State

The runtime model is deliberately explicit.

Evaluation happens relative to:

- an environment object
- a continuation object
- a current evaluator state

The evaluator state shapes are:

```text
{ :eval { :expr expr, :env env, :cont cont } }
{ :ret  { :value value, :cont cont } }
```

The current continuation vocabulary is:

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

This is the important shift away from the retired kernel: control state is no
longer smuggled back into the language as evaluator-generated lambdas. The
machine state is ordinary Click data.

## Step Protocol

`step` operates on one explicit evaluator state and returns one explicit
response object:

```text
{ :continue next }
{ :return value }
{ :error info }
```

That keeps success, suspension, and failure in the language model rather than
in host-side side channels.

Current runtime errors include:

- applying a non-closure
- reading an unbound variable
- malformed executable shapes
- matching with zero overlaps
- matching with more than one overlap
- using `:set` with a non-object receiver or non-symbol key

## Evaluation Strategy

The intended strategy is small-step and local:

- one step inspects one explicit state
- one step returns one explicit response object
- environments are extended explicitly during closure application
- substitution is not the runtime model

The host convenience evaluator repeatedly calls `step` until it reaches
`:return` or `:error`.

## Current Rust Surface

The Rust API is centered on the reflective core:

- raw term constructors such as `Term::symbol` and `Object::with`
- helper constructors for executable shapes such as `var`, `lambda`, `apply`,
  `match`, and `set`
- `parse` and `parse_many`
- `step`
- `eval` and `eval_in_env`
- `run_source` as a host convenience wrapper over parsed source text

`run_source` is a convenience API, not a settled statement about the eventual
top-level language. The core language semantics are still term-level and
state-machine-level.

## Deliberate Omissions

The current active language does not have a built-in typed kernel, primitive
records-vs-sums distinction, a trusted proof checker, quote syntax, or the old
list-oriented metaprogramming primitives.

The historical `bootstrap/` tree remains useful as a record of earlier
experiments, especially the lesson that explicit environments are often simpler
than substitution-heavy reflective evaluators.

## Open Questions

- What should the top-level program model be for files that contain more than
  one term?
- Should `match` stay exact-single-overlap, or should it grow a richer pattern
  discipline?
- How should `match` behave on bare symbols?
- Is `:set` enough for computed object construction, or does the core want an
  additional helper?
- What should a typing or proof-checking layer look like above this raw
  computation core?
