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

The kernel should be described first by two calculi:

- the object calculus: symbols, records, and expressions that manipulate them
- the proof calculus: claims, proof objects, and rules for deriving claims

The trusted Rust implementation provides structural equality, evaluation, and
proof checking as algorithms over those calculi.

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

The object calculus is lambda calculus plus immutable record operations. This is
the source language of the kernel.

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
```

`|` marks sum alternatives. `:quote` injects raw data into computation.
Variable lookup is explicit with `:var`. Record operations provide the
fundamental data structure.

Operations are written as tagged objects. `:get` reads one key, `:with` returns
an updated record, `:has` returns `:true` or `:false`, `:equal` uses structural
equality, and `:if` branches on `:true` or `:false`.

## Object Calculus Evaluation

The object calculus needs an evaluator, but the evaluator is an algorithm over
the calculus rather than the first kernel concept. A CEK machine is the current
small-step implementation strategy.

```text
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

Evaluating a lambda returns a closure. Applying a closure extends the closure
environment with the parameter binding.

## Evaluation Rules

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

## Initial Evaluation Claims

The first proof checker can prove exact finite evaluation traces:

```text
(:equal (:left Object :right Object))

(:step-equals
  (:input EvalState
   :output EvalOutcome))

(:returns
  (:input EvalState
   :value Value))
```

`returns` is the large-step claim. It means repeated evaluator steps eventually
return `value`.

Minimum proof forms:

```text
(:equal-structural ())                 // structural equality
(:step ())                             // run the trusted evaluator once
(:returns-return (:step p1 :equal p2))  // one step returns
(:returns-next (:step p1 :rest p2))     // one step continues
```

This proves `((lambda x. x) :ok) evaluates to :ok`, and gives immediate tests
for shadowing, closure capture, evaluation order, `:get`, and errors.

## Proof Calculus Claims

Finite traces are not enough for theorem proving. The proof calculus starts as
first-order logic over objects, plus primitive claims about object-calculus
evaluation:

```text
LogicObject = Object, possibly containing (:logic-var Symbol)

Claim =
  (:true ())
  (:false ())
  (:equal (:left Object :right Object))
  (:step-equals (:input EvalState :output EvalOutcome))
  (:returns (:input EvalState :value Object))
  (:terminates (:input EvalState))
  (:and (:left Claim :right Claim))
  (:or (:left Claim :right Claim))
  (:not Claim)
  (:implies (:if Claim :then Claim))
  (:forall (:var Symbol :claim Claim))
  (:exists (:var Symbol :claim Claim))
```

Every `Object` position inside a claim may be a `LogicObject`. `terminates` is
shorthand for `exists value: returns(input, value)`.
Variables in claims are proof variables, represented by `:logic-var`, not CEK
`:var` expressions. Quantifier elimination substitutes an object for matching
logic-variable occurrences.

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

## Proof Calculus

Proofs are derivation objects for claims. The checker is the trusted algorithm:
`check : Context -> Claim -> Proof -> ok | error | diverge`. `Context` holds
definitions and labeled assumptions.

Core proof forms:

```text
(:use Symbol)                         // use assumption or proven lemma
(:equal-structural ())                // run structural equality
(:step ())                            // run the trusted evaluator once
(:returns-return (:step Proof :equal Proof))
(:returns-next (:step Proof :rest Proof))
(:true-intro ())
(:false-elim (:proof Proof))
(:and-intro (:left Proof :right Proof))
(:and-left Proof)
(:and-right Proof)
(:or-left Proof)
(:or-right Proof)
(:or-elim (:proof Proof :left Proof :right Proof))
(:not-intro (:assume Symbol :body Proof))
(:not-elim (:not Proof :positive Proof))
(:implies-intro (:assume Symbol :body Proof))
(:implies-elim (:function Proof :arg Proof))
(:forall-intro (:var Symbol :body Proof))
(:forall-elim (:proof Proof :value Object))
(:exists-intro (:value Object :proof Proof))
(:exists-elim (:proof Proof :witness Symbol :body Proof))
(:rewrite (:equal Proof :body Proof))
(:unfold Symbol)
```

The checker rules are syntax-directed:

- `:use` proves a claim if the named context claim is structurally equal.
- `:equal-structural` proves equal objects; `:step` proves one evaluator step.
- `:returns-return` and `:returns-next` prove `:returns` by finite traces.
- `:true-intro` proves `:true`; `:false-elim` proves any claim from `:false`.
- `:and`, `:or`, `:not`, and `:implies` use standard natural-deduction rules.
- `:forall-elim` and `:exists-intro` substitute object values for logic vars.
- `:implies-intro`, `:not-intro`, and `:exists-elim` extend local assumptions.
- `:forall-intro` checks the body with a fresh logic variable.
- `:rewrite` uses proved equality; `:unfold` expands a context definition.

Induction is intentionally left out of this first proof calculus.
