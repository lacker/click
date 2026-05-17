# Click Design

This document records the current design direction for `click`.

Click is now a reflective computation core first. The earlier typed-kernel-first
design has been retired from the active language.

## Goal

The Click kernel should be reflectively complete: Click should be able to
represent Click programs, computations, types, proofs, evaluators, and checkers
as Click data and computations, and should be able to check meaningful proofs
about those mechanisms.

Reflective completeness is the design test for kernel features. The kernel
should have enough primitive power to internalize its own metatheory, but not so
much that ordinary language features become trusted syntax. New forms, type
systems, proof systems, and effect disciplines should be built as Click
artifacts that elaborate into the trusted core.

That means the base language should compute. Computation is not an add-on to a
pure proof language; it is the substrate that later typing and proof layers
reason about.

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
