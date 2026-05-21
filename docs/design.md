# Click Philosophy and the Type System

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

# Click Kernel Requirements

* A universal object format. One stupid data model with structural equality.

* A minimal CEK machine in the kernel, exposed as a small-step relation.

* A proof checker that validates proof objects against claim objects.

* Powerful enough to define basic data types, like lists, and prove theorems about them, like reverse(reverse(xs)) = xs.

* Powerful enough to define and check type systems from the lambda cube: λ→, λP, λ2, λC

* Powerful enough to model real languages: WebAssembly, LLVM IR, C, JavaScript, TypeScript, Python

## Do not modify this line or anything above it. That zone is for human use.
## Below this line is for AI use. Keep this document capped at 300 lines.

## Revised Kernel Proposal

The kernel trusted base should stay small:

- `Object`
- structural equality
- one minimal CEK stepper
- one proof checker

Everything else should be represented as explicit objects: data types, typing
judgments, proof systems, tactics, language semantics, and extra checkers.

## Object Model

```text
Object = Symbol | Record
Record = finite map from Symbol to Object
```

These are refinements over `Object`, not primitive runtime variants:

```text
Expr <: Object
Value <: Object
Environment <: Record
Continuation <: Object
EvalState <: Record
EvalOutcome <: Record
Claim <: Record
Proof <: Record
```

The kernel has stupid structural equality: symbols by name, records by keys and
values.

## CEK Machine

The CEK machine is in the kernel. It gives Click one tiny trusted model of
computation.

```text
Expr =
  Symbol
  (:var Symbol)
  (:lambda (:param Symbol :body Expr))
  (:apply (:function Expr :arg Expr))

Value =
  Symbol
  (:closure (:param Symbol :body Expr :env Environment))

Environment = Record(Symbol -> Value)

Continuation =
  :halt
  (:after-function
    (:arg Expr
     :env Environment
     :then Continuation))
  (:after-argument
    (:function Value
     :then Continuation))

EvalState =
  (:eval
    (:expr Expr
     :env Environment
     :continuation Continuation))
  (:continue
    (:value Value
     :continuation Continuation))

EvalOutcome =
  (:next EvalState)
  (:return Value)
  (:error Object)

cek_step : EvalState -> EvalOutcome
```

A bare symbol is a literal value. Variable lookup is explicit with `:var`.
Evaluating a lambda captures the current environment. Applying a closure extends
the closure environment with the parameter binding. No substitution in this
demo.

## CEK Rules

```text
eval Symbol -> continue(Symbol, c)
eval (:var name) -> continue(env[name], c), or error (:unbound name)
eval (:lambda (:param p :body body)) -> continue(closure(p, body, env), c)
eval (:apply (:function f :arg x)) -> eval(f, env, after-function(x, env, c))
continue(function_value, after-function(x, env, c)) ->
  eval(x, env, after-argument(function_value, c))
continue(arg_value, after-argument(closure(p, body, closure_env), c)) ->
  eval(body, extend(closure_env, p, arg_value), c)
continue(value, :halt) -> return value
```

If the function is not a closure, return `(:error (:not-a-function value))`.

## Finite Trace Proofs

The first proof checker can prove exact finite CEK traces:

```text
(:object-equal (:left Object :right Object))

(:cek-step-equals
  (:input EvalState
   :output EvalOutcome))

(:cek-evals-to
  (:input EvalState
   :value Value))
```

`cek-evals-to` is the large-step claim. It means repeated `cek_step` calls
eventually return something structurally equal to `value`.

Minimum proof forms:

```text
(:object-equal ())                      // structural equality
(:cek-step ())                          // run trusted cek_step once
(:cek-return (:step p1 :equal p2))       // one step returns
(:cek-next (:step p1 :rest p2))          // one step continues
```

The checker rules:

```text
cek-return: if one step returns actual, and actual = expected,
  then input evaluates to expected.

cek-next: if one step reaches next_input, and next_input evaluates to expected,
  then input evaluates to expected.
```

This proves:

```text
((lambda x. x) :ok) evaluates to :ok
```

It also gives immediate tests for shadowing, closure capture, evaluation order,
and non-function errors.

## Reverse-Reverse Target

The requirements ask for something much stronger:

```text
for all lists xs:
  reverse(reverse(xs)) = xs
```

This cannot be proved with finite trace proofs alone. It needs a proof layer
that can state and check general theorems.

## Predicate Types

Types should be predicates on `Object`, not a second kernel data model:

```text
Predicate = Object -> Claim

(:satisfies (:value Object :predicate Predicate))
```

Basic type formers can be ordinary predicate combinators:

```text
Unit(x) = x = ()
Product(:head A :tail B)(x) = Record(x) and A(x.:head) and B(x.:tail)
Sum(:nil Unit :cons Cons)(x) = exactly one variant tag, with valid payload
```

So lists do not need to be kernel-declared inductive types. They can be a
recursive predicate built from sums and products:

```text
List(A) =
  recursive X.
    Sum(
      :nil Unit,
      :cons Product(:head A :tail X))
```

Example list:

```text
(:cons
  (:head :a
   :tail (:cons
     (:head :b
      :tail (:nil ())))))
```

## Needed Proof Power

To prove `reverse(reverse(xs)) = xs`, Click needs generic proof forms for:

```text
(:forall (:var Symbol :where Predicate :claim Claim))
(:implies (:if Claim :then Claim))
(:object-equal (:left Object :right Object))
```

It also needs definitions for functions over these predicate-shaped data:

```text
append((:nil ()), ys) = ys
append((:cons (:head x :tail xs)), ys) =
  (:cons (:head x :tail append(xs, ys)))

reverse((:nil ())) = (:nil ())
reverse((:cons (:head x :tail xs))) =
  append(reverse(xs), (:cons (:head x :tail (:nil ()))))
```

And proof rules for:

- introducing and instantiating `forall`
- introducing and applying `implies`
- unfolding named definitions
- rewriting by equality
- induction for recursive predicates like `List(A)`
- importing and applying proven lemmas

## Axioms

We should not add theorem-specific kernel axioms. Adding
`reverse(reverse(xs)) = xs` as an axiom would prove nothing about the kernel.

But theories do need assumptions. The useful split is:

- kernel rules are trusted and tiny
- theory axioms are explicit objects
- recursive predicates can expose explicit induction principles

For the list theorem, the trusted/generic part should be the recursive-predicate
induction schema, not the result. The list theory supplies `List`, `append`, and
`reverse`. The proof supplies the induction argument.

A real reverse-reverse proof probably needs these induction lemmas:

```text
append(xs, nil) = xs
append(append(xs, ys), zs) = append(xs, append(ys, zs))
reverse(append(xs, ys)) = append(reverse(ys), reverse(xs))
reverse(reverse(xs)) = xs
```

Open design question: should `append` and `reverse` be CEK programs, rewrite
equations, or both? The theorem is easier to state with equations. The language
is more coherent if equations can be justified by CEK programs later.
