# Make `step` simple across a call precondition

## Status

P2. This is what remains of the 2026-09 kernel-search cleanup, whose other
work has landed: the kernel contains no production proposition prover, the
logical search lives in `src/surface/planning/proposition_search.rs`, and
every other kernel consumer decides by exact routes or emits an obligation
(see the kernel authority boundary in
[proof-objects.md](../docs/internals/proof-objects.md)). One route is left.

## Violated invariant

A simple tactic requests one deterministic checked operation and does no
search. `step()` over a call is classified simple, but when the callee's
precondition is not exactly available at the call, the step driver
discharges it by search: `StatementPrerequisitePolicy::Planning` in
`src/surface/proof/execution_planning/transition_certification.rs` asks
the planner for a derivation and checks it before accepting. The check
makes this sound. It is still search inside a simple step, and its success
leaves no trace: no `have` enters the proof, `click expand` prints a bare
`step()`, and the expansion re-verifies only because the same search runs
again on re-check. Every other smart success expands to explicit Surface
Click; this one does not.

The kernel side is already done: `prepare_verified_function_call` emits a
requirement the exact routes miss as `ProofObligation::verification_condition`
with the context `"<callee> precondition"` and the lowering-provenance
chain that `intro` consumes. The gap is purely on the surface: the emitted
requirement is discharged as a prerequisite instead of being presented as
a goal the proof states.

## Intended design

An emitted requirement becomes an ordinary goal closed before the step.

- The step driver reports an unresolved requirement as structured data
  (proposition, context, provenance chain) rather than discharging it.
- The smart planner synthesizes the requirement's Surface spelling, applies
  a real `have <requirement> by { ... }` operation on the `Proof` before the
  step, closes its body with checked steps, and retains it, so expansion
  prints the `have` and a certificate without it is rejected. The `have`'s
  goal must be the reported proposition up to alpha-equivalence (binder
  identity and `Exists` name blind, exact otherwise), since contract
  lowering and fixed-state lowering allocate binders from different ranges.
- An explicit proof states the requirement with `have` or `assumption`
  before the step; the exact route then discharges it and no obligation is
  raised. This already works today and is the manual escape hatch.
- The `Planning` leg is deleted. `step()` over a call is then simple: exact
  routes only.

## What exists

Two attempts landed the mechanism but not the closure; the second is
preserved on branch `claude/simplify-kernel-pkg-10c2-requirement-goals-2`
(red, a checkpoint, never integrate as is). It has the structured
`UnresolvedRequirement` on `ClickError`, `Proof::step_discharging_reported_requirements`
with the planned `have` installed under `ProofScope::with_recorded_goal_introductions`
so `intro` consumes the chain, and `propositions_are_alpha_equal` with unit
tests. It discharges seven of the twelve affected fixtures.

Prerequisites already landed on master: emitted requirements carry the
provenance chain; existential lowering places definedness guards under
their binder as body conjuncts (an implication there would be vacuously
satisfiable); loads through foreign static objects and `loadable(p[a..b])`
ranges over an external argument synthesize and round-trip.

## Remaining gaps

Twelve fixtures have automatic proofs that rely on the hidden discharge:
`cstr_dynamic_indexed_read`, `cstr_dynamic_indexed_read_requires_permission`,
`cstr_dynamic_loadability`, `stdlib_external_contracts`,
`exists_loadable_range`, `forall_loadable_range`, `file_scope_static_arrays`,
`static_array_parity_scalar`, `static_array_parity_multidimensional`,
`static_array_parity_fixed_multidimensional`, `static_local_arrays`,
`contract_refinement_uses_implied_requirement`, plus `examples/bounded-pool`
and `examples/owned-string`. Their C and their proofs stay as they are; the
planner must close them. Two capabilities are missing:

1. **Planning a witness, a snapshot transport, and range coverage together.**
   For the `cstr` family the goal is
   `exists len. (not overflows(len + 1) and loadable(bytes[len..len + 1]) and ...)`.
   After `witness`, the body owes a loadability at the current point while
   the covering `loadable(bytes[0..len + 1])` sits at the caller's entry
   snapshot. `simp` closes the coverage alone and the covering range alone;
   no planner selects the `transport` source and composes the three. The
   hand-written form in `mdtests/cstr_readable_witness_stated_before_call.md`
   shows the target shape. The premise set is the named call arguments and
   their recorded facts; do not scan ambient facts.
2. **A spelling for a load-defining equation.** `examples/bounded-pool` and
   `examples/owned-string` raise requirements whose head conjunct is
   `Var(loadvar) == load(snapshot, p)`, which `synthesize_surface_proposition`
   cannot write. Add the synthesizer with a round-trip test, as the static
   and range spellings were added.

Also known: `auto` reports it has no explicit simple certificate for an
existential over `CInt32`, pre-existing.

## Intended regression

`mdtests/call_precondition_disjunction_is_an_obligation.md` with
`by { execute(); simp(); }`: the expansion contains
`have x > 0 or y > 0 by { left(); }` before the step, re-verifies through
the ordinary entry point, and is rejected when that `have` is deleted. The
twelve fixtures above verify unchanged and their expansions print the
discharging `have`. A requirement with a hidden guard in front of a written
implication introduces both in order through the chain. Requirement
checking is flat in unrelated caller facts.

## Acceptance criteria

- `StatementPrerequisitePolicy::Planning` and the checked-derivation leg in
  `transition_certification.rs` are deleted; `step()` discharges a call
  requirement by exact routes only.
- Every emitted call requirement in both fixture harnesses is closed by a
  retained `have` that expansion prints, or by an explicit one in the
  source; the twelve fixtures and two examples above verify with their
  current C and proof text.
- No new kernel rule, no new `ProofStep` variant, no grammar change, no
  ambient-fact scan in the planner.
- `scripts/check.sh` passes with the body-rerun census pinned at zero.

## Not in scope

Recursive-call `decreases` at a call site: the recursive-edge check is a
syntactic walk in `termination.rs`, not search, and emitting it as a call
obligation needs the caller's termination plan at the call site, which the
whole-program termination pass does not provide. The `arithmetic` smart
tactic is [arithmetic.md](arithmetic.md).
