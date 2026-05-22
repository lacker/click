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

These are refinements or aliases over `Object`, not primitive runtime variants:

```text
Expr <: Object
Value = Object
Closure <: Record
Environment <: Record
Continuation <: Object
EvalState <: Record
EvalOutcome <: Record
Claim <: Record
Proof <: Record
```

The kernel has stupid structural equality: symbols by name, records by keys and
values.

## Kernel Object Calculus

The kernel CEK machine evaluates a tiny object calculus: lambda calculus plus
immutable record operations.

```text
Expr =
  | (:quote Object)
  | (:var Symbol)
  | (:lambda (:param Symbol :body Expr))
  | (:apply (:function Expr :arg Expr))
  | (:get (:record Expr :key Symbol))
  | (:with (:record Expr :key Symbol :value Expr))
  | (:has (:record Expr :key Symbol))
  | (:equal (:left Expr :right Expr))
  | (:if (:cond Expr :then Expr :else Expr))

Closure = (:closure (:param Symbol :body Expr :env Environment))
Value = Object

Environment = Record(Symbol -> Value)

Continuation =
  | :halt
  | (:after-function (:arg Expr :env Environment :then Continuation))
  | (:after-argument (:function Value :then Continuation))
  | (:after-get (:key Symbol :then Continuation))
  | (:after-with-record
      (:key Symbol :value Expr :env Environment :then Continuation))
  | (:after-with-value (:record Record :key Symbol :then Continuation))
  | (:after-has (:key Symbol :then Continuation))
  | (:after-equal-left (:right Expr :env Environment :then Continuation))
  | (:after-equal-right (:left Value :then Continuation))
  | (:after-if
      (:then-branch Expr :else-branch Expr :env Environment :then Continuation))

EvalState =
  | (:eval (:expr Expr :env Environment :continuation Continuation))
  | (:continue (:value Value :continuation Continuation))

EvalOutcome =
  | (:next EvalState)
  | (:return Value)
  | (:error Object)

cek_step : EvalState -> EvalOutcome
```

`|` marks sum alternatives. `:quote` injects raw data into computation.
Variable lookup is explicit with `:var`. Evaluating a lambda returns a closure.
Applying a closure extends the closure environment with the parameter binding.
Record operations provide the fundamental data structure.

## Calculus Rules

```text
eval (:quote value) -> continue(value, c)
eval (:var name) -> continue(env[name], c), or error (:unbound name)
eval (:lambda (:param p :body body)) -> continue(closure(p, body, env), c)
eval (:apply (:function f :arg x)) -> eval(f, env, after-function(x, env, c))
continue(value, :halt) -> return value
```

Any form that evaluates subexpressions uses continuation frames. `:apply`
evaluates function then argument. `:get`, `:with`, `:has`, `:equal`, and `:if`
evaluate their inputs left-to-right.

Record operation results:

```text
get(record, key) -> value, or error (:missing-field key) / (:not-a-record value)
with(record, key, value) -> updated record, or error (:not-a-record value)
has(value, key) -> :true if value is a record with key, else :false
equal(left, right) -> :true or :false by structural equality
if(:true, then, else) -> then
if(:false, then, else) -> else
if(other, then, else) -> error (:bad-condition other)
```

## Finite Trace Proofs

The first checker can prove exact finite CEK traces:

```text
(:equal (:left Object :right Object))

(:step-equals
  (:input EvalState
   :output EvalOutcome))

(:returns
  (:input EvalState
   :value Value))
```

`returns` is the large-step claim. It means repeated `cek_step` calls
eventually return `value`.

Minimum proof forms:

```text
(:equal-structural ())                 // structural equality
(:step ())                             // run trusted cek_step once
(:returns-return (:step p1 :equal p2))  // one step returns
(:returns-next (:step p1 :rest p2))     // one step continues
```

This proves `((lambda x. x) :ok) evaluates to :ok`, and gives immediate tests
for shadowing, closure capture, evaluation order, `:get`, and errors.

## General Claims

Finite traces are not enough for theorem proving. The next kernel target is a
small claim language:

```text
Claim =
  (:equal (:left Object :right Object))
  (:step-equals (:input EvalState :output EvalOutcome))
  (:returns (:input EvalState :value Object))
  (:terminates (:input EvalState))
  (:and (:left Claim :right Claim))
  (:implies (:if Claim :then Claim))
  (:forall (:var Symbol :claim Claim))
  (:exists (:var Symbol :claim Claim))
```

`terminates` is shorthand for `exists value: returns(input, value)`.
Variables in claims are proof variables, not CEK `:var` expressions.

Types are predicates:

```text
Predicate = Object -> Claim
(:satisfies (:value x :predicate P)) means P(x)
```

So `List(x)` can mean "`is_list(x)` returns `:true`", not "x belongs to a
kernel-declared inductive type".

`field(r, k, v)` is not primitive. It means `:get` returns `v`:

```text
returns(initial_state((:get (:record (:quote r) :key k))), v)
```

## Proof Language

The checker is contextual: `check : Context -> Claim -> Proof -> ok | error |
diverge`. `Context` holds definitions and labeled assumptions. Core forms:

```text
(:use Symbol)                         // use assumption or proven lemma
(:equal-structural ())                // run structural equality
(:step ())                            // run trusted cek_step once
(:returns-return (:step Proof :equal Proof))
(:returns-next (:step Proof :rest Proof))
(:and-intro (:left Proof :right Proof))
(:and-left Proof) / (:and-right Proof)
(:implies-intro (:assume Symbol :body Proof))
(:implies-elim (:function Proof :arg Proof))
(:forall-intro (:var Symbol :body Proof))
(:forall-elim (:proof Proof :value Object))
(:exists-intro (:value Object :proof Proof))
(:exists-elim (:proof Proof :witness Symbol :body Proof))
(:rewrite (:equal Proof :body Proof))
(:unfold Symbol)
(:object-cases (:scrutinee Object :branches Record))
(:object-induction (:var Symbol :body Proof))
```

## Recursion Axiom

The generic recursion principle should be structural induction over finite
objects, not list-specific induction. It is based on `:get`.

```text
To prove forall x: P(x),
prove P(x) assuming:
  P(part) for every proper part reachable from x
  by one or more successful :get operations.
```

Since `Object` values are finite trees, `:get` paths are well-founded.

This is the base axiom that should prove termination of structurally recursive
programs. For `is_list`, the recursive call is on the tail field, which is a
part reached through two `:get` operations: first `:cons`, then `:tail`.

## List Theory Target

The list demo should be the second artifact:

```text
nil = (:nil ())
cons(h, t) = (:cons (:head h :tail t))

is_list(x) returns :true or :false
List(x) := is_list(x) returns :true

rev_acc(x, acc)
reverse(x) = rev_acc(x, nil)
```

Targets:

```text
forall x: terminates(is_list(x))
forall x acc:
  List(x) and List(acc) implies
  exists y: returns(rev_acc(x, acc), y) and List(y)
forall x:
  List(x) implies exists y: returns(reverse(x), y) and List(y)
```

This is enough before trying `reverse(reverse(xs)) = xs`.
