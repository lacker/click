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

Propositions can talk about arbitrary computations. Quantifiers may be
unguarded, or guarded by propositions such as `is-value`, `is-list`,
`is-effect`, and `is-outcome`. Rust APIs that require a concrete finalized
result use `Value`, `Effect`, or `Outcome`. Errors are named effects, not a
second channel for returning structured values.

Boolean values are reserved quoted symbols: `:true` and `:false`. They are not
a separate kernel value variant, but the kernel has an `if` computation form
that branches on exactly those two quoted symbols. A non-boolean condition
reduces to a runtime error; condition errors and divergence propagate, and only
the selected branch is evaluated. The kernel also has a `symbol-eq` computation
form for comparing finalized quoted symbols. It returns `:true` only when both
operands are the same quoted symbol, returns `:false` for other finalized
values, and propagates effects.

The kernel also has a `value-kind` computation form for broad value
introspection. After evaluating its input, it returns `:symbol`, `:lambda`, or
`:list`, and propagates effects. Lists are one value kind; use `list-case` to
distinguish `nil` from `cons`. Prelude helpers use `value-kind` to define
boolean value predicates and `value-eq`, a structural equality for symbols and
lists that errors on lambdas.

At the source level, `(is-bool x)` is proposition shorthand for saying that `x`
computes to either `(quote :true)` or `(quote :false)`. It elaborates to an
ordinary disjunction, not to a separate primitive proposition.

Kernel variables are computation variables. Facts about those variables live in
propositions, including quantifier guards and local proof assumptions. This
keeps the kernel from having a second built-in "type-ish" bookkeeping layer
beside ordinary propositions.

List values are proper by construction: `nil` and `cons` build list values, and
a finalized cons tail must itself be a list. Raw computations can still contain
open or malformed cons-shaped expressions until evaluation and proof reasoning
settle them. The kernel uses `is-list` guards and list induction to reason over
list values.

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
`any`, `all`, `is-symbol`, `is-lambda`, `is-list-value`, `value-eq`, `last`,
`init`, `null`, and `is-singleton`, plus theorems about those definitions. Prelude
booleans use the kernel's reserved quoted symbols.
The list prelude itself lives in `src/prelude/list.lisp`; the corresponding
Rust module only includes that source file, with list-specific Rust helpers kept
as test support.
