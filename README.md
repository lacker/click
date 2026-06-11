# click

`click` is a new programming language.

Click's goal is to make it easy to add proofs to existing programs in other programming languages.

Some principles for the design of the kernel:

Simplicity
It should be clear to an AI how to prove things that seem obvious.
When a proof fails, it should be clear what went wrong.
Proofs should be AI-comprehensible. Human-comprehensible is nice to have but not critical.
Proofs do not need to be concise.
The kernel should be clear and explicit, not necessarily minimal.

Flexibility
It is very important to handle C.
It is also important, later, to handle C++, Rust, JavaScript, TypeScript, and Python.
Eventually we must handle tricky parts like concurrency and mutable state.
Handling advanced mathematics is a non-goal.

Click is designed in three layers:

1. A core calculus with computations, values, effects, outcomes, propositions,
   and proofs. Based on a Lisp-like untyped list value.
2. An LCF-style logistical layer for naming, scoping, checking, and safely
   reusing definitions and theorems.
3. A flexible language modeling system.

The medium-term goal is to prove useful facts about C code.

## Human edited above this point, AI edited below this point.

## C target

The medium-term target is to prove useful facts about C code, not to finish a
general-purpose theorem prover in the abstract. C should be the forcing case for
syntax, tactics, language modeling, and any future type-system work.

The first C target should be a deliberately small C subset, tentatively called
`C0`:

- integer expressions
- specifically, real `int32` values rather than natural-number stand-ins
- local variables
- assignment
- sequencing
- `if`
- `return`
- simple function bodies after statement semantics are working

The first semantic model should make undefined behavior and runtime errors
explicit. C has many behaviors that are not ordinary returned values, so the C
model should use outcome-style judgments rather than pretending every program
just returns a value.

The first useful proof targets should be small but recognizable C functions:

- `max`: prove the result is at least both inputs and equals one of them
- `abs`: prove the result is nonnegative, with explicit assumptions about the
  integer range where C signed overflow is not triggered
- `clamp`: prove the result lies inside the requested interval
- a simple counted loop: prove a bounds-safety property

The first genuinely compelling demo should involve memory safety, probably an
array or pointer loop with a proof that every read is in bounds. Arithmetic
examples are useful for bootstrapping, but the eventual pitch to C programmers
should be about facts they already care about: no out-of-bounds access, no
undefined behavior under stated preconditions, and correct return values.

Current status:

- There is a tiny hand-built C0 model in `src/lang/c/`.
- The model has source values for C types, expressions, statements,
  environments, stores, expression outcomes, and statement outcomes.
- C integers are represented as tagged `int32` values containing a kernel
  `bv32` payload, with primitive signed less-than, wrapping addition, and signed
  overflow checks. This is still tiny, but it is no longer using `nat` as a
  substitute for C integers.
- C undefined behavior is represented as ordinary C outcome values, not as
  Click kernel errors. Signed `int32` addition now returns UB on overflow.
- The first judgments are in place: `c-has-type`, `c-stmt-well-typed`,
  `c-eval-expr`, and `c-exec-stmt`.
- The checked theorem set includes determinism facts for expression and
  statement execution, preservation-style facts for `int32` literals, concrete
  less-than and addition evaluations, an overflow-to-UB theorem, a UB
  propagation theorem through `return`, a well-typedness proof for a tiny `max`
  body, and concrete execution theorems for `max(0, 1)` and `max(1, 0)`.
- The full C theorem load is part of the normal test suite again; concrete
  `int32` arithmetic proofs no longer rely on reducing 32-bit boolean lists.
- Symbolic branch theorems for `max` are not done yet. The current obstacle is
  the interaction between call-by-value constructor evaluation and rewriting a
  symbolic `(c-int32-lt a b)` condition under the C execution model.
- The existing S-expression source format is acceptable for bootstrapping the C
  model, but proof and model syntax should be revisited once C examples start
  getting large.
- Type-system design should be driven by C modeling work. For now, C types
  should be represented as ordinary values and C typing should be represented by
  ordinary propositions and judgments.

Near-term implementation shape:

1. Strengthen the symbolic rewrite/control-flow story enough to prove symbolic
   branch theorems for `max`.
2. Add a tiny expression/statement pretty syntax so C examples are less
   parenthesis-heavy.
3. Add parsing/import from real C syntax only after the hand-built AST model is
   coherent.

Deferred C features:

- pointers and arrays
- loops with invariants
- function calls
- structs and unions
- integer width coverage beyond `int32`, overflow, promotions, and
  signed/unsigned conversion
- volatile and atomics
- concurrency
- preprocessor and build-system integration

## Current architecture

The kernel lives in `src/kernel/`:

- `calculus.rs` defines the core calculus entities: `Computation`, `Value`,
  `ErrorName`, `Effect`, `Outcome`, `Prop`, and `Proof`.
- `eval.rs` implements reduction and normalization for computations.
- `check.rs` implements substitution, alpha-equivalence, and the primitive proof
  rules.
- `theory.rs` contains the logistical LCF-style layer: `Theory`, `Theorem`,
  `ProofContext`, and named bindings.

The source elaborator lives in `src/elab/`. It parses S-expression source and
proof scripts, then elaborates them into kernel computations, propositions, and
proofs. `SourceEnv` owns the mapping from source spellings to opaque kernel
`Name` and `Symbol` IDs. `ProofContext` is separate: it is the local set of
assumptions available while checking or elaborating one proof goal. The prelude
uses this layer to load source files into a `Theory`; when source names matter,
the loaded prelude carries both the checked `Theory` and its `SourceEnv`.
Concrete numeric IDs are not part of the prelude's public API; callers resolve
source spellings through the source environment.
General source loading uses `LoadedSource`, which can load source strings or
files into a checked `Theory` while maintaining the shared `SourceEnv`.
Source loading can attach a section name to each parsed module; prelude loading
uses names such as `list/value_eq` and `nat/sub`, and diagnostics for parse,
computation, and theorem failures carry that section when one is available.

Source theorems can still use raw kernel-like proof terms with `(proof ...)`.
They can also use goal-directed tactic scripts with `(by ...)`. Tactics inspect
the current goal and local context, then elaborate to ordinary kernel `Proof`
values that are checked by the kernel. The initial tactic set is intentionally
small and deterministic: `intro`, `assumption`, `exact`, `eval`, `apply`,
`have`, `specialize`, `obtain`, `cases`, `rewrite`, `fold`, `simp`, `simpa`,
`or-elim`, `list-induction`, `value-induction`, `calc`, `split`/`constructor`,
`exists`, `left`, and `right`.
Continuation tactics such as `have`, `specialize`, `obtain`, and `cases` can
either scope over the remaining tactic script or take an explicit final
`(by ...)` body to make the scope boundary visible in source.
Raw proof scripts still accept lower-level kernel proof forms such as
`forall-elim` and `exists-elim`; these are escape hatches for direct proof terms,
not goal-directed tactics.

The simplifier tactic is deliberately explicit for now: `(simp only rule ...)`
uses only the listed proof expressions as rewrite rules, plus kernel reduction.
Rules are tried in source order. A rule may be a theorem, a local proof
assumption, or a proof expression; if it proves a conjunction, equality-bearing
conjuncts are tried as rewrite rules and non-equality conjuncts are ignored.
Simp rewrites left-to-right, infers forall arguments by matching the rule's
left-hand side, discharges available premises from the local context, and
rewrites inside subcomputations before falling back to reduction. It does not
yet have global `[simp]`-style rule tags.

By convention, simp rules should be oriented toward canonical forms. Avoid
using expansion rules with `simp`, especially reverse-direction rules that
introduce a reducible definition or alias. Since simplification interleaves
rewriting with kernel reduction, an expansion can immediately reduce back to
the original term and form a cycle. Use `fold` when a proof should present a
kernel-normal term using a source-level definition name, and use explicit
`rewrite` followed by `eval` for other one-shot expansion steps. For example,
`zero` computes to `nil`, so `zero_eq_nil` is naturally a simp rule in the
`zero -> nil` direction; the reverse direction should be written as `(fold
zero)` rather than as a simp rule.

The related `(simpa only rule ... using proof)` tactic simplifies the equality
goal and the equality proven by `proof`, then closes the goal if the simplified
sides match. `(simpa only rule ...)` is the proof-free form and behaves like a
terminal simplification proof.

When a proof needs the finalized result of a computation, use `obtain` to name
that result and its computation proof. For example, `(obtain sum sum_proof
(add_computes_to_list left right) ...)` introduces a value `sum` and a proof
that `(add left right)` computes to `sum`. Later steps should use `sum_proof`
directly with `exact` when that is the current goal, or with `rewrite`, `simp
only`, or `simpa only` to move between the named witness and the original
computation. This is the same proof shape as Lean code like `obtain <sum,
hsum> := add_computes_to_list left right` followed by `exact hsum`, `rw
[hsum]`, or `simpa [hsum] using ...`: it is just existential elimination plus
rewriting, not a special Click-only proof concept.

By convention, name the computation proof after the witness, such as
`sum_proof` for `sum`; use a more specific proof name only when destructing an
existential that carries additional semantic facts.

Propositions can talk about arbitrary computations. Kernel quantifiers are
plain binders. Source syntax may attach a predicate to a quantifier as
shorthand: `(forall x P Q)` elaborates to `forall x. P -> Q`, and
`(exists x P Q)` elaborates to `exists x. P and Q`. Rust APIs that require a
concrete finalized result use `Value`, `Effect`, or `Outcome`. Errors are named
effects, not a second channel for returning structured values.

Kernel equality is the proof-level equality proposition. The source proposition
`(computes-to computation result)` is readability-oriented syntax for that same
equality relation; it elaborates to `equal computation result`, and the kernel
does not give it a separate proof rule. Use `computes-to` when the right side is
being presented as an evaluation result, and `equal` when the statement is
symmetric or algebraic.

The raw equality proof tools are direct kernel proof forms. `eval-to` proves
that a computation reduces to a stated result, while `eval-same` proves equality
by reducing two computations to the same normal form. `symm` and `trans` are
symmetry and transitivity for proof equality. `rewrite` transports a proof
across an equality inside a proposition template. `symbol-eq-true` is a bridge
from the computational boolean `(symbol-eq left right)` returning `:true` to
proof equality of `left` and `right`.

Boolean values are reserved quoted symbols: `:true` and `:false`. They are not
a separate kernel value variant, but the kernel has an `if` computation form
that branches on exactly those two quoted symbols. A non-boolean condition
reduces to a runtime error; condition errors and divergence propagate, and only
the selected branch is evaluated. The kernel also has a `symbol-eq` computation
form for comparing finalized quoted symbols. It returns `:true` only when both
operands are the same quoted symbol, returns `:false` for other finalized
values, and propagates effects. Since `symbol-eq` is a computation rather than
a proposition, proofs use bridge rules such as `symbol-eq-true` to turn a proof
that `(symbol-eq left right)` computes to `:true` into proof equality of `left`
and `right`.

The kernel also has a `value-kind` computation form for broad value
introspection. After evaluating its input, it returns `:symbol`, `:lambda`, or
`:list`, and propagates effects. Lists are one value kind; use `list-case` to
distinguish `nil` from `cons`. Prelude helpers use `value-kind` to define
boolean value predicates and `value-eq`, a structural equality for symbols and
lists that errors on lambdas. Like `symbol-eq`, `value-eq` is a computation;
the list prelude proves `value_eq_sound`, which turns a `:true` result from
`value-eq` into proof equality. It also proves comparability facts for any
successful `value-eq`, `value_eq_refl` for values accepted by
`value-eq-comparable`, and `value_eq_symm` for successful comparisons.

At the source level, `(is-bool x)` is proposition shorthand for saying that `x`
computes to either `(quote :true)` or `(quote :false)`. It elaborates to an
ordinary disjunction, not to a separate primitive proposition.

Kernel variables are computation variables. Facts about those variables live in
ordinary propositions, including predicate premises and local proof assumptions.
This keeps the kernel from having a second built-in "type-ish" bookkeeping
layer beside ordinary propositions.

List values are proper by construction: `nil` and `cons` build list values, and
a finalized cons tail must itself be a list. Raw computations can still contain
open or malformed cons-shaped expressions until evaluation and proof reasoning
settle them. The kernel uses `is-list` predicates and list induction to reason
over list values.

The kernel has both list induction and value induction. List induction reasons
over a list spine. Value induction reasons over all finite values: symbols,
lambdas, `bv32` values, nil, and cons, with recursive hypotheses for both the
cons head and tail. The head hypothesis is what makes proofs about nested list values
possible; ordinary list induction only gives a hypothesis for the tail.

The core calculus can contain opaque names. The logistical layer gives those
names meaning by binding them to computations or theorems. Human-facing spelling,
scoping, modules, and imports belong to the logistical layer, not to the core
calculus.

Prelude source definitions may use direct named recursion: a definition can
refer to its own source name, and the logistical layer resolves that name to the
opaque kernel computation name. Since divergence is already part of the
computation model, recursive definitions are allowed; proofs still justify any
claimed equality by finite unfolding and reduction.

Surface expressions belong outside the core calculus. The elaborator uses
S-expressions as input and elaborates them into kernel computations,
propositions, and proofs.

Raw computations and propositions may be open. This is useful for templates,
quantifier bodies, and proof checking under local assumptions. Kernel theorems
are closed: a `Theorem` can only be constructed when its proposition has no
free variables. Named computation definitions are also closed. Concrete
`Value`, `Effect`, and `Outcome` values have no variable form; an open value is
represented as a computation variable plus a proposition such as `is-value`.

The standard prelude is just a theory built on top of the kernel. It currently
contains list definitions such as `reverse_acc`, `reverse`, `append`, `snoc`,
`concat`, `length`, `take`, `drop`, `split-at`, `nth`, `replicate`, `map`,
`concat-map`, `fold-right`, `fold-left`, `zip`, `unzip`, `zip-with`, `filter`,
`partition`, `any`, `all`, `find`, `is-symbol`, `is-lambda`, `is-list-value`,
`value-eq`, `value-eq-comparable`, `member`, `elem-index`, `last`, `init`,
`null`, and `is-singleton`, plus theorems about those definitions. Prelude
booleans use the kernel's reserved quoted symbols.
It also contains unary natural-number definitions such as `zero`, `succ`,
`is-nat-value`, `is-zero`, `pred`, `range`, `add`, `sub`, `mul`, `nat-eq`,
`nat-le`, and `nat-lt`, with arithmetic and comparison theorems.
The list prelude itself lives in ordered source sections under
`src/prelude/list/`; the corresponding Rust module only includes those source
files, with list-specific Rust helpers kept as test support.

Some prelude APIs use plain list encodings rather than extra kernel value
variants. A pair is a two-element list `(cons first (cons second nil))`; its
first projection is `head`, and its second projection is `head` after `tail`.
Options use `none = :none` and `some value = (:some value)`. The predicates
`is-none` and `is-some` recognize those conventions, including rejecting
malformed `:some` lists. Unary natural numbers are lists of `unit`, so `nil` is
zero and `(cons unit n)` is successor.
