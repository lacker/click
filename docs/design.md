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

* A small step relation that implements the CEK machine.

* A proof checker that validates proof objects against claim objects.

* Powerful enough to encode basics, like a list type, and that reversing a list twice is the identity.

* Powerful enough to define and check the lambda cube: λ→, λP, λ2, λC

* Powerful enough to model real languages: WebAssembly, LLVM IR, C, JavaScript, TypeScript, Python

## Do not modify this line or anything above it. That zone is for human use.
## Below this line is for AI use.

## Minimum Kernel Demo Proposal

Goal: implement a tiny CEK evaluator and prove:

```text
((lambda x. x) :ok) evaluates to :ok
```

This is the smallest useful demo because it forces lambdas, closures,
environments, continuations, small steps, and a large-step proof.

## Pseudo-Types

Everything is represented as `Object`. A symbol is a primitive object. A
record is a compound object:

```text
Object = Symbol | Record
Record = finite map from Symbol to Object
```

The rest of these are refinements, not primitive runtime variants:

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

## CEK Expressions

```text
Expr =
  Symbol
  (:var Symbol)
  (:lambda (:param Symbol :body Expr))
  (:apply (:function Expr :arg Expr))
```

A bare symbol is a literal value. Variable lookup is explicit with `:var`.

## CEK Values

```text
Value =
  Symbol
  (:closure (:param Symbol :body Expr :env Environment))
```

Closures are where binding happens. Evaluating a lambda captures an
environment. Later, inert records can also be values.

## Environments

```text
Environment = Record(Symbol -> Value)
```

Examples:

```text
()
(:x :ok)
```

Environment extension is record update. No substitution in this demo.

## Continuations

```text
Continuation =
  :halt
  (:after-function
    (:arg Expr
     :env Environment
     :then Continuation))
  (:after-argument
    (:function Value
     :then Continuation))
```

`Continuation` means what to do with a value that has just been produced.

## EvalState

```text
EvalState =
  (:eval
    (:expr Expr
     :env Environment
     :continuation Continuation))
  (:continue
    (:value Value
     :continuation Continuation))
```

`(:eval ...)` inspects an expression. `(:continue ...)` feeds a value to a
continuation. This is the CEK split.

## EvalOutcome

```text
EvalOutcome =
  (:next EvalState)
  (:return Value)
  (:error Object)
```

```text
cek_step : EvalState -> EvalOutcome
```

This is the precise version of `step : Term -> Outcome<Term>` for the first
demo.

## CEK Step Rules

```text
eval Symbol:
  next continue(Symbol, c)

eval (:var name):
  next continue(env[name], c)
  error (:unbound name) if missing

eval (:lambda (:param p :body body)):
  next continue((:closure (:param p :body body :env env)), c)

eval (:apply (:function f :arg x)):
  next eval(f, env, (:after-function (:arg x :env env :then c)))

continue(function_value, (:after-function (:arg x :env env :then c))):
  next eval(x, env,
    (:after-argument (:function function_value :then c)))

continue(arg_value,
  (:after-argument
    (:function (:closure (:param p :body body :env closure_env))
     :then c))):
  next eval(body, extend(closure_env, p, arg_value), c)

continue(value, :halt):
  return value
```

If the function is not a closure, return `(:error (:not-a-function value))`.

## Claims

The minimum checker needs these claims:

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

## Proofs

Minimum proof forms:

```text
(:object-equal ())                      // structural equality
(:cek-step ())                          // run trusted cek_step once
(:cek-return (:step p1 :equal p2))       // one step returns
(:cek-next (:step p1 :rest p2))          // one step continues
```

The checker rules:

```text
(:cek-return (:step p1 :equal p2))
  p1 proves (:cek-step-equals (:input input :output (:return actual)))
  p2 proves (:object-equal (:left actual :right expected))
  therefore proves (:cek-evals-to (:input input :value expected))

(:cek-next (:step p1 :rest p2))
  p1 proves (:cek-step-equals (:input input :output (:next next_input)))
  p2 proves (:cek-evals-to (:input next_input :value expected))
  therefore proves (:cek-evals-to (:input input :value expected))
```

Errors do not prove `:cek-evals-to`. We can add error claims later.

## Demo Trace

Initial state:

```text
s0 =
(:eval
  (:expr (:apply
    (:function (:lambda (:param :x :body (:var :x)))
     :arg :ok))
   :env ()
   :continuation :halt))
```

Claim:

```text
(:cek-evals-to (:input s0 :value :ok))
```

Trace shape:

```text
s0 -> s1  eval application
s1 -> s2  eval lambda into closure
s2 -> s3  after-function, eval argument
s3 -> s4  eval literal :ok
s4 -> s5  after-argument, enter closure body with x = :ok
s5 -> s6  eval (:var :x)
s6 -> :ok
```

The proof is just nested `:cek-next` ending in `:cek-return`, with every
one-step proof being `(:cek-step ())`.

This is a real minimum demo. If this works, we have:

- object representation
- lambda binding by environment
- closures
- continuations
- one trusted small-step function
- proof that the small-step function returns a claimed outcome
- proof that many small steps evaluate to a value

## What This Does Not Solve Yet

No mutation/store, recursion, surface syntax, tactics, foreign languages,
parallel stepping, or proof that a Rust implementation of `cek_step` matches a
Click definition. Those should be later layers.
