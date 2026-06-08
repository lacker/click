# click

`click` is a new programming language.

Click's goal is to make it easy to add proofs to existing programs in other programming languages.

The general idea is to make an extremely flexible kernel and theorem proving system.

English is very flexible. You can cram all sorts of stuff into an English sentence.
Even if it is kind of disgusting. Like sushi burrito hors d'oeuvres.

Click aims to do the same thing, for programming languages.

Click is designed in three layers:

1. A core calculus with computations, values, effects, outcomes, propositions,
   and proofs. Based on a Lisp-like untyped list value.
2. An LCF-style logistical layer for naming, scoping, checking, and safely
   reusing definitions and theorems.
3. A structural type system, where a value can belong to many types.

The medium-term goal is to build out layers 1 and 2.
* Keep code quality high. Clean up when things should be cleaned up.
* Make a prelude that loads from `.lisp` files.
* Build out lots of definitions and proofs about lists, to make sure layers 1 and 2 are well designed.
* Make sure to prove props about props. Like proving strong induction.

It's better to have n simple things, rather than one thing with n different ways to interpret it.
The "many simple things" principle.
So it's okay if the kernel feels like a "pile of different algebraic types".

## Current architecture

The kernel lives in `src/kernel/`:

- `calculus.rs` defines the core calculus entities: `Computation`, `Value`,
  `ErrorName`, `Effect`, `Outcome`, `Prop`, and `Proof`.
- `eval.rs` implements reduction and normalization for computations.
- `check.rs` implements substitution, alpha-equivalence, and the primitive proof
  rules.
- `theory.rs` contains the logistical LCF-style layer: `Theory`, `Theorem`,
  `Context`, and named bindings.

The source elaborator lives in `src/elab/`. It parses S-expression source and
proof scripts, then elaborates them into kernel computations, propositions, and
proofs. `ElabEnv` owns the mapping from source spellings to opaque kernel
`Name` and `Symbol` IDs. The prelude uses this layer to load source files into a
`Theory`; when source names matter, the loaded prelude carries both the checked
`Theory` and its `ElabEnv`. Concrete numeric IDs are not part of the prelude's
public API; callers resolve source spellings through the elaborator environment.
General source loading uses `LoadedSource`, which can load source strings or
files into a checked `Theory` while maintaining the shared `ElabEnv`.

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
lambdas, nil, and cons, with recursive hypotheses for both the cons head and
tail. The head hypothesis is what makes proofs about nested list values
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
`concat`, `map`, `concat-map`, `fold-right`, `fold-left`, `zip-with`, `filter`,
`any`, `all`, `is-symbol`, `is-lambda`, `is-list-value`, `value-eq`,
`value-eq-comparable`, `member`, `last`, `init`, `null`, and `is-singleton`,
plus theorems about those definitions. Prelude booleans use the kernel's
reserved quoted symbols.
The list prelude itself lives in ordered source sections under
`src/prelude/list/`; the corresponding Rust module only includes those source
files, with list-specific Rust helpers kept as test support.
