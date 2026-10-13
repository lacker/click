# SMT auto, stage 1: in-house arithmetic and equality

Design for stage 1 of [smt-auto](../issues/smt-auto.md). Click gets its own
SMT-style decision procedure for linear integer arithmetic, machine-integer
bridging and equality with constructors. A proof calls it through `auto`.
Every success is turned into ordinary checked proof steps, which
`click expand` prints. Code references are to master at `52a77c2d`.

## Goals

- Close the arithmetic and equality obligations that proofs now discharge by
  hand: `to_integer` bridges, `arithmetic() using { ... }` lists,
  transitivity chains, and one-line rewrite equalities.
- Read premises from the proof context. The author does not list them.
- Expand every success into simple steps that the kernel already checks,
  plus two small new kernel certificate forms.
- Fail promptly within a deterministic work budget. A failure names the
  fragment it left, or gives a counterexample.

## Non-goals

- Quantifiers, recursive definitions, nonlinear arithmetic beyond opaque
  atoms, and bit-level reasoning. These come in later stages.
- Changing `simp`. That waits for the stage-1 measurements.
- Search completeness. The procedure is complete for its stated fragment
  within budget, and nothing more is promised.

## What the baseline shows

In `examples/rust-byte-sum` and `examples/bounded-pool`, most of the
arithmetic is not linear reasoning. It moves facts between machine integers
and `Integer`, one stdlib theorem at a time:

```click
have to_integer(i) < to_integer(bytes.len()) by {
    apply(uint64_less_than_to_integer(i, bytes.len())) using { i < bytes.len(); }
}
```

These are followed by `arithmetic() using` steps that list the bridged facts
again. A pure linear arithmetic solver closes none of these goals unless the
bridging is automatic too. So stage 1 has three theories, not two: linear
integer arithmetic, machine-integer bridging, and equality with
constructors.

## What exists today

- **Integer certificate.** Nodes are `Premise`, `Scale`, `Add`,
  `EqualityToLessEqual`, `EqualityFromBounds` and `Trivial`
  (`src/kernel/proof/integer_arithmetic.rs`). The checker recomputes every
  node, and the conclusion must equal the goal's normalized claim.
- **Integer planner.** `plan_integer_affine_certificate`
  (`src/surface/checking/integer_affine_planner.rs`) matches premises,
  pairs (by Cramer's rule) and triples, and eliminates equalities. It is
  not simplex, and it only sees listed premises.
- **`simp`.** It selects premises through a connected component of atomic
  facts that the frozen kernel decider must first decide
  (`smart_closures.rs:1918`). The decider is deliberately weak on `Integer`
  goals, so non-trivial `Integer` goals need `using`.
- **Equality graph.** `src/kernel/equality_graph.rs` is a trusted
  union-find with congruence. It has no explanation API, and it covers
  neither `Integer` terms nor algebraic constructors.
- **Machine-to-`Integer` bridges.** About 40 stdlib theorems, such as
  `int32_add_to_integer` and `uint64_less_than_to_integer`.
- **Work budgets.** `record_deterministic_work`,
  `deadline_exceeded_with_work` and the nestable `with_run_work_limit`
  (`src/instrumentation.rs`).

## Architecture

```
auto
  └─ solver::prove(goal, frontier)             src/surface/solver/   (untrusted search)
       ├─ select premises                      indexed, connected to the goal
       ├─ purify into atoms                    Integer atoms, machine atoms, ADT terms
       ├─ bridge theory                        machine facts ⇄ Integer facts, with justifications
       ├─ EUF + constructors                   congruence closure with explanations
       ├─ LIA                                  general simplex over rationals, cuts, branch and bound
       ├─ combination                          equality sharing between EUF and LIA
       └─ certificate builder                  → Vec<ProofStep>
  └─ apply each ProofStep through the kernel   (trusted check, unchanged path)
```

The solver never adds a fact to the kernel. Its only output is a list of
ordinary `ProofStep`s. `Proof::apply_step` applies them, and they become the
tactic's recorded provenance, which `click expand` prints.
`arithmetic() using` already works this way: it records itself as a
concrete `ArithmeticCertificate` step (`step_application.rs:846`).

### Solver interface

```rust
pub trait Solver {
    fn prove(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome;
}
pub enum Outcome {
    Proved(Certificate),            // theory-level proof, turned into ProofSteps
    Refuted(Model),                 // counterexample over the atoms, for diagnostics
    Outside(FragmentReason),        // the goal left the fragment, with the reason
    Exhausted(Frontier),            // budget ran out, with the frontier reached
}
```

`Problem` holds atoms and literals with their source facts. A `Certificate`
holds Farkas multipliers, equality explanations and bridge instances. An
external solver would implement the same trait, and its results would still
go through the same certificate builder.

### Premise selection

Take the facts that the frontier holds as available pure facts. Start from
the goal's atoms and follow the existing per-variable fact indexes
(`condition_facts_by_variable`, `signed_order_bounds` and their `int64`
form) to facts that share an atom. Collect the connected component, charging
work per fact visited. The component never scans the whole context. This
replaces `MAX_BOUND_VARIABLES = 8`: the work budget is the only limit.

Stage 1 adds one index: `Integer` comparison facts by atom. Today only the
`int32` and `int64` signed-order indexes exist.

### Theory 1: linear integer arithmetic

- **Simplex.** A general simplex with bound explanations, in the style used
  by Yices and Z3, over `num-bigint` rationals. It works incrementally on
  atoms. When it finds a conflict, the explanation gives a nonnegative
  combination of the asserted bounds: the Farkas multipliers.
- **Integrality.** A strict `Integer` inequality is tightened to `≤` with
  `+1`, as the kernel already does. A rational solution with a fractional
  atom gets a Chvátal–Gomory cut when the conflict row allows one, and
  otherwise a bounded branch and bound. Each split is recorded and becomes a
  case split in the certificate.
- **Refutation form.** The solver proves `goal` by refuting
  `premises ∧ ¬goal`. Over the integers, `¬(a ≤ b)` is `b + 1 ≤ a`, and an
  equality goal is two `≤` goals.

### Theory 2: machine-integer bridging

Every machine-typed term `m` that appears in a selected fact, or in the
goal, becomes the atom `to_integer(m)`. Each bridge fact the solver uses is
justified by a stdlib theorem, which the certificate applies.

| Machine fact or term | `Integer` fact the solver may use | Justification |
|---|---|---|
| any `m : intN`/`uintN` | type range bounds on `to_integer(m)` | `*_to_integer_bounds` (some widths missing: add them) |
| `a < b`, `a <= b`, `a == b` (same type) | the same relation on `to_integer` | `*_less_than_to_integer`, `*_less_equal_to_integer`, … |
| goal `a < b` on machine values | `Integer` goal, then back | `*_to_integer_less_than_implies_less_than`, … |
| `a + b`, `a - b` (signed) with `defined(a op b)` available or provable | `to_integer(a op b) == to_integer(a) op to_integer(b)` | `int32_add_to_integer`, `int64_subtract_to_integer`, … |
| `a + b` (unsigned) with the sum provably in range | the same equation | `uint64_add_to_integer` (premise is the range fact, which the solver proves first) |
| goal `defined(a op b)` (signed) | two range goals | `int32_add_defined_by_integer_bounds`, … |
| casts `(T)x` | equality when the value is provably in range | `integer_cast_identity` node in the `rules` family |

Bridge instances are created lazily. A term gets its range bounds when the
term enters the problem. An operation's equation is added only when a
conflict involves the operation's result atom, so the bridge work stays
proportional to the terms the proof touches. A wrapping unsigned operation
without a provable range stays opaque in stage 1. A modular encoding comes
later.

### Theory 3: equality with constructors

- **Congruence closure.** A new untrusted union-find with a proof forest, so
  each derived equality can be explained as a chain of input equalities and
  congruence steps. The trusted kernel `EqualityGraph` is not changed.
- **Constructor rules.**
  - Injectivity: `C(x̄) = C(ȳ)` gives `xᵢ = yᵢ`.
  - Disjointness: `C(x̄) = D(ȳ)` with `C ≠ D` is a conflict.
  - Field selection on a known constructor.
- **Terms.** These rules range over `AlgebraicTerm`, `Integer` and machine
  terms, and over pure-function applications as uninterpreted functions.
- **Certificate output.** An explanation turns into kernel steps that already
  exist:
  - `rewrite(P)` steps, with `P` an available or already-derived equality;
  - `extract` for constructor injectivity;
  - `contradiction` for disjoint constructors.

### Combination

The theories are combined by equality sharing between EUF and LIA, in the
Nelson–Oppen style. When the simplex fixes two shared atoms to the same
value by tight bounds, the equality goes to EUF; when EUF merges two atoms
that occur in arithmetic, the equality goes to the simplex. Integer
arithmetic is not convex, so this combination is incomplete for some
disjunctive equalities. That is accepted and documented: such goals fail
within budget with `Outside`.

Boolean structure in stage 1 is limited:

- a conjunctive goal is split;
- an implication whose antecedent is available is used;
- a disjunctive premise is case-split only when the case count stays within
  the budget.

There is no general DPLL in stage 1.

## Kernel changes

The kernel gets two additions to the `Integer` certificate. Both are local
and easy to check.

1. **Refutation conclusion.** `conclusion_by_refutation N`: node `N` derives
   `0 ≤ -k` with `k > 0` from the listed premises plus the negated goal,
   which is the certificate's premise 0. The checker verifies that premise
   0 is exactly the integer negation of the goal. With this, Farkas
   multipliers need no rescaling of the goal coefficient, which the current
   form cannot express.
2. **Rounding node.** `divide N by g`: from `Σ cᵢ·xᵢ + k ≤ 0` where `g > 0`
   divides every `cᵢ`, derive `Σ (cᵢ/g)·xᵢ + ⌈k/g⌉ ≤ 0`. This is the
   Chvátal–Gomory step. The checker charges work by bit size, like the
   existing nodes.

Case splits from branch and bound use the existing proof `if` at the
surface. No kernel change is needed for them.

## Integration

**`auto` is the only entry point.** Decided 2026-10-12: `auto` closes the
current goal by any means.

- **At a function proof's frontier**, the goal is to reach exit with every
  obligation met. `auto` executes the remaining C, then tries the solver on
  each remaining obligation before the current `simp` ladder. The fallback
  keeps every existing proof working.
- **On a proposition**, such as `have P by auto;` or a theorem body, there
  is no C to execute, so `auto` is the solver alone. Today `auto` is refused
  inside a `have`; that refusal goes away.
- **In a loop's `preserve` body**, execution would stop at the back edge,
  not at function exit. Milestone 5 checks this case.

There is no separate `smt` tactic. Use `have P by auto;` to call the solver
without executing C.

`arithmetic()` is unchanged. Bare `arithmetic()` proves an arithmetic goal
from its own terms, and `arithmetic() using { ... }` proves it from the
listed premises.

Whether `have P;` with no proof should mean `have P by auto;` instead of
`have P by simp;` is part of the `simp` question. That question waits for the
stage-1 measurements.

**Expansion.** `auto` expands into the steps the solver
emitted. For the `rust-byte-sum` bound the expansion would be:

```click
have to_integer(total) <= 255000 by {
    apply(uint64_less_than_to_integer(i, bytes.len())) using { i < bytes.len(); }
    apply(uint64_less_equal_to_integer(bytes.len(), 1000u64)) using { bytes.len() <= 1000u64; }
    arithmetic_certificate {
        premise 0: not to_integer(total) <= 255000 => 255001 <= to_integer(total);
        ...
        conclusion_by_refutation 7;
    }
}
```

**Diagnostics.**

- `Refuted` prints a counterexample over the source atoms, for example
  `fails when to_integer(i) = 1000 and to_integer(total) = 255001`.
- `Outside` names the term that left the fragment, for example `a * b with
  two symbolic factors is opaque`.
- `Exhausted` gives the work spent and the frontier reached.

All three are bounded in size.

**Budget.** The solver runs inside a nested `with_run_work_limit` inside the
smart-tactic budget. It charges work per simplex pivot, per union-find
operation and per bridge instance. The default limit is calibrated on the
regression cases, as `TacticWorkLimits` was.

## Performance

The search is superlinear in the worst case, as any simplex is. That is
allowed for smart tactics under
[verification-efficiency](../docs/internals/verification-efficiency.md),
because the bound is the budget and the output is a certificate whose
checking is linear in its size. An expanded proof never calls the solver.
Premise selection uses indexes and is charged per fact. A deterministic
scaling regression checks that solver work grows linearly with the number of
independent obligations in a function, and does not grow with unrelated
facts.

## Module layout

```
src/surface/solver.rs                 trait, Problem, Outcome, entry point
src/surface/solver/select.rs          premise selection
src/surface/solver/atoms.rs           purification, atom table
src/surface/solver/simplex.rs         general simplex, explanations, cuts
src/surface/solver/euf.rs             congruence closure with proof forest, constructors
src/surface/solver/bridge.rs          machine-integer bridge theory
src/surface/solver/combine.rs         equality sharing, case splits
src/surface/solver/certificate.rs     theory proof → Vec<ProofStep>
src/kernel/proof/integer_arithmetic.rs  + refutation conclusion, divide node
```

## Milestones

Each milestone is one PR, green and useful on its own.

1. **Kernel forms.** Add the refutation conclusion and the divide node,
   with surface syntax, mdtests (positive and negative) and reference
   documentation.
2. **Simplex core.** Add the simplex with Farkas output and its certificate
   builder. `have P by auto;` uses it on selected `Integer` facts. Add unit
   tests and a scaling regression.
3. **Bridges.** Add the bridge theory and any missing `*_to_integer_bounds`
   theorems. Rewrite `rust-byte-sum` with the solver and record its size and
   time.
4. **Equality.** Add EUF with constructors and the combination. Rewrite
   one arm of `rbtree_erase_color_flips_red_all.click` and record its size
   and time. The first step, landed, is a bounded search for a chain of
   checked `rewrite` steps over the connected equalities, closed by
   `assumption`, `normalize` or a budgeted `simp`; the numbers are in
   [smt-auto](../issues/smt-auto.md). Congruence closure, injectivity and
   disjointness, and the combination with the simplex remain.
5. **`auto` integration.** Make the solver the first closer in `auto`.
   Rewrite `bounded-pool` and record the numbers. Report the stage-1
   measurements in [smt-auto](../issues/smt-auto.md) and decide on stages
   2–4 and on `simp`.

## Risks

- **Bridge theorems not yet in stdlib.** Some widths or operations have no
  bridge theorem yet. Missing ones are added as stdlib theorems, so the
  kernel trusts nothing new.
- **Rendering gaps.** Every intermediate claim has to be spelled in source
  for `click expand`. `integer_plan_to_surface_certificate` already reports
  rendering gaps; the solver treats such a gap as a failure, not as a proof
  that cannot be printed.
- **Sharing with the existing ladder.** The existing `simp` ladder stays as
  the fallback. If both are kept, a goal may be closed by different routes
  as the code evolves, which makes expansions less stable. Stage 1's
  measurements decide whether the ladder's `Integer` and signed planners
  can be retired.
