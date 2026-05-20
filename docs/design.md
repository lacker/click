# The Click Type System

Click's goal is to make it easy to prove things about programs, no matter
what language those programs are written in.

This means that Click needs a very flexible model for programs, computations, types,
proofs, evaluators, and checkers.

Click does need a rigorous kernel. But practical programs are often mutable, partial,
asynchronous, nondeterministic, or weakly typed. They can panic or have undefined behavior.
Click needs to be accepting of all these things.

The prover should fit any program, rather than requiring programs to be
reshaped until they look natural to the prover.

To achieve this flexibility, Click's type system is based on refinement types and subtypes.
In Click, everything is an "object". Types are represented by predicates on objects.

The Curry-Howard correspondence shows us that in a sense, proofs and types are the same thing.
In traditional dependent type systems, the kernel implements a powerful type system, and then we build proofs based on types.
Click works the other way around: we build a powerful proof system, and then we build types based on proofs.

The upshot is that the Click type system becomes very flexible. Any type in any programming language
can be naturally represented as a Click type.

# The Click Kernel

The kernel implements:

Object (type):
think of it like untyped, simplified JSON.
An object can either be an opaque "symbol", or a map of symbols to objects.

Term (type):
things that "look like executable things". There's some encoding for lambdas, maybe closures.
Term is a subtype of object.

Outcome (type):
a wrapper, only used around term, that represents monadic computation-type value. Like done/continue/error.

Since the type system is built on top of the proof system, we can't rely on the type system to ensure that
functions are only called on arguments of the right type, or that a program terminates. That's why we need to represent
the concepts of "error" and "infinite loop" in the kernel.

step (function):
Term -> Outcome<Term>
The "small step" of the kernel.

TODO: how to prove stuff?


## Do not modify this line or anything above it. That zone is for human use.
## Below this line is for AI use.

## Kernel Target

Below this line, the design question is deliberately narrow: what is the
smallest kernel that can talk about objects, computation, equality, proofs, and
checking?

The kernel should have:

- raw objects
- one built-in top type, `:Object`
- structural object equality
- `step : Term -> Outcome<Term>`
- large-step equality claims built from small steps
- proof objects checked against explicit claims

Everything else should earn its place by making a concrete proof easier.

## Raw Objects

The kernel's raw data language is:

```text
Term ::= Symbol | Object(Symbol -> Term)
```

There are no primitive lists, functions, closures, records, sums, products, or
source-language types. Those are object conventions.

The current S-expression syntax is only notation for this raw data.

## Object Type

The kernel has one built-in top type:

```text
(:has-type (:term t :type :Object))
```

Every well-formed raw term has type `:Object`. Richer types are refinements of
`:Object`, not new primitive kernel domains.

For example, list-ness is a refinement over objects shaped like:

```text
(:nil ())
(:cons (:head h :tail t))
```

## Structural Equality

The kernel has built-in structural equality:

```text
(:object-equal (:left a :right b))
```

This equality is intentionally stupid:

- symbols are equal iff their names are equal
- objects are equal iff they have the same keys and equal values at each key
- object field order does not matter
- symbols and objects are never equal

This is not program equivalence or mathematical equality in a user theory. It
is the base comparison operation the checker can trust directly.

## Small Step

Pseudo-type notation:

```text
Outcome<T> =
  (:next T)
  (:return T)
  (:error Term)

step : Term -> Outcome<Term>
```

So yes: the input to `step` is a term, and one step produces an outcome whose
payloads are also terms.

The input term is the whole steppable state. If we need a machine tag, it lives
inside the term:

```text
(:state (:machine :click-seq :data ...))
```

That means we do not need `step(machine, state)` as the first shape. We can get
that back by convention:

```text
step((:state (:machine m :data s)))
```

If a term is not meaningful to step, `step` can return an error:

```text
(:error (:not-steppable term))
```

A proof-facing claim says what one call to `step` returns:

```text
(:step-equals (:input state :outcome outcome))
```

Version zero can prove this from explicit assumptions. Later, checked step
rules can prove the same claim without changing large-step checking.

## Monadic Smell

`next`, `return`, and `error` look monadic. This seems important.

Roughly:

- `(:return value)` is the pure/finished case
- `(:next state)` is "keep going in this computation"
- `(:error info)` is a distinguished effectful exit

The kernel should probably not contain `bind` yet. But the shape of
large-step proofs is already bind-like: prove one step, then continue proving
the rest from the next state.

Maybe the right rule is: the kernel understands the tiny operational monad of
stepping, while richer monads live as object-level machines with laws proved
about them.

## Large-Step-Equals

The kernel has large-step equality claims:

```text
(:large-step-equals (:input state :value expected))
```

This means that repeated calls to `step` eventually return a value structurally
equal to `expected`.

This is not a host evaluator. It is a checked finite proof over `:step`.

Return proof:

```text
(:large-return
  (:step step_proof
   :actual actual_value
   :equal equal_proof))
```

The checker verifies:

```text
step_proof proves
  (:step-equals (:input state :outcome (:return actual_value)))

equal_proof proves
  (:object-equal (:left actual_value :right expected))
```

Continue proof:

```text
(:large-continue
  (:next next_state
   :step step_proof
   :rest rest_proof))
```

The checker verifies:

```text
step_proof proves
  (:step-equals (:input state :outcome (:next next_state)))

rest_proof proves
  (:large-step-equals (:input next_state :value expected))
```

An `:error` outcome does not prove `:large-step-equals`. If error behavior
matters, it should get a separate large-step claim.

## Proof Checking

The trusted kernel operation is:

```text
check(context, claim, proof) -> (:ok claim) | (:error info)
```

Initial proof forms:

- `(:assume name)` checks when `context[name]` is exactly the target claim
- `(:object-type)` checks `:has-type` for a well-formed raw term and `:Object`
- `(:object-equal)` checks structural equality directly
- `(:step-rule ...)` or `(:assume name)` proves `:step-equals`
- `(:large-return ...)` checks the return rule above
- `(:large-continue ...)` checks the continue rule above

This is enough to check finite computation traces before we have tactics,
induction, or checked evaluator rules.

## Reverse List Test

A concrete test is proving that a reverse program returns the expected object
for one input list.

Input:

```text
(:cons
  (:head :a
   :tail (:cons
     (:head :b
      :tail (:cons
        (:head :c
         :tail (:nil ()))))))
```

Expected:

```text
(:cons
  (:head :c
   :tail (:cons
     (:head :b
      :tail (:cons
        (:head :a
         :tail (:nil ()))))))
```

The first kernel-level goal is:

```text
(:large-step-equals
  (:input reverse_initial_state
   :value expected))
```

The first proof can be an explicit finite trace whose steps are assumptions.
That will be tedious, but it tests the kernel boundary. Once this works, the
next design pressure is obvious: replace assumed steps with checked step rules.

## Current Rust Experiment

The current Rust evaluator hardcodes `:var`, `:lambda`, `:apply`, `:match`, and
`:set`. It is useful as an experiment, but too specific to be the kernel.

The direction here is to keep raw terms and move trust into explicit proof
checking for small-step and large-step claims.

## Open Questions

- Is `step : Term -> Outcome<Term>` really enough, with machine tags inside
  terms?
- Should explicit step assumptions exist in v0, or should checked step rules be
  part of the first implementation?
- What is the smallest useful step-rule language?
- Should `:large-step-equals` also expose final states, not just returned
  values?
- Do we need a sibling claim for large-step errors?
- What is the smallest refinement layer over `:Object`?
