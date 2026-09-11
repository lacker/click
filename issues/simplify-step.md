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

## What has been established

Two attempts built the mechanism and measured what it closes. Nothing from
them is on master; the design below is the retained result, and the next
implementation starts from it rather than from a branch.

**Reporting the requirement.** In `transition_certification.rs`, the
`Contextual` arm's checked-derivation leg is gated on
`obligation.is_assumable()`, so a required verification condition gets no
derivation leg. The refusal carries a structured payload,
`UnresolvedRequirement { proposition, context, introductions }`, on
`ClickError` (a private field with an accessor), built from the obligation
itself: its proposition, its context label such as `"strlen precondition"`,
and the package 17 chain from `ProofObligation::introductions()`. The
payload must survive unmodified up to `apply_step(ProofStep::Step)`; the
step drivers re-wrap errors on the way up and each re-wrap must forward it.

**Planning the `have`.** `Proof::step_discharging_reported_requirements`
wraps the statement step. On a reported requirement it synthesizes the
written form under a `QualifiedSynthesisScope`, `begin_have`s it, requires
the scope's goal to match the reported proposition (see the comparison
below), installs the obligation's chain with a new
`ProofScope::with_recorded_goal_introductions` so `intro` consumes the
recorded chain rather than one re-lowered from the synthesized text, closes
the body with the shared smart-closure vocabulary, and `join`s, which
retains an ordinary `ProofStep::Have` ahead of the `Step`. The loop is
bounded structurally: each planned `have` must discharge a requirement not
already discharged, so it is limited by the statement's distinct
obligations. `ConstructionEvidence::CertifiedStatementStep` in
`surface_construction.rs` is never reached for a smart `execute()`, because
the smart step planner applies `ProofStep::Step` directly; the `have` has
to be a real proof operation, not rendered evidence.

**One goal for construction and discharge.** A freshly lowered `have`
never compares equal to the kernel's requirement under derived
`PartialEq`: contract lowering allocates quantifier binders from 3,100,000
and fixed-state lowering from 2,000,000, and `Exists` includes its binder
name in equality while synthesis names binders `__click_qN`. The retained
answer is `propositions_are_alpha_equal`: `Exists` and `ForAll` compare
sorts, freshen both bodies to one variable, and recurse, ignoring the
binder name; `And`/`Or`/`Implies`/`Not` recurse; every other pair is exact
equality. It is deliberately stricter than the older
`propositions_alpha_equivalent`, which also canonicalizes loads. Load
naming is handled separately by `proposition_in_canonical_load_form`,
applied to both sides first, because contract lowering spells a load out
where `have` lowering names it. The planner accepts a `have` by that
comparison and the kernel discharges by the same one:
`PureFactContext::states_required_goal` takes condition leaves through the
exact indexed route and compares a quantified leaf against the quantified
facts alone, so unrelated facts are never visited. Unit tests to keep:
binder identity ignored; existential binder name ignored; binders
introduced under every connective; a differing non-binder subterm
rejected; a free-variable capture rejected; a differing quantifier
rejected.

**Presentation fixes that were needed.** `Exists` synthesis recovers the
binder name the contract wrote instead of generating `__click_qN`; `intro`
keys a universal's binding by the name the written body mentions rather
than the recorded chain's, so a proof that restates a kernel-built goal in
its own words resolves its own binder; the named-range loadability
synthesizer also spells a range whose byte count folded to an element
count, reading the start from the base pointer's own index. When a kernel
conjunction the written form does not spell is split with `both`, and one
conjunct is the lowering's own definedness guard, the written form travels
with the other conjunct, so the arm below it can still be rendered; the
arm still owes exactly its kernel conjunct.

**Closing the planned body.** The shared smart vocabulary, plus: a kernel
conjunction the written form does not spell is split with `both`; an
existential names a witness from the call's own arguments, then zero, then
each of the caller's own existential requirements through `choose`; the
requirement is spelled literally, and failing that with its leading
definedness-guard conjuncts left to the lowering that regenerates them.

**Measured reach.** With the three prerequisites below landed, that
mechanism discharged seven of the twelve affected fixtures by a planned
`have`, plus the two hand-written spelling fixtures
(`static_local_array_requirement_stated_explicitly`,
`loadable_range_requirement_stated_explicitly`), which had relied on the
deleted leg for conjunction splitting. Body shapes seen: the static family
gets one `have` of the whole six-conjunct requirement closed by nested
`both`/`rewrite`/`normalize`; `forall_loadable_range` gets
`intro(); intro(); simp();`; `exists_loadable_range` gets `witness` plus
`both`. The `cstr` fixtures' universal requirement
`forall k. 0 <= k and k < len implies loadable(bytes[k..k + 1])` also
closes once the written form travels across the guard split.

**Prerequisites already on master.** Emitted requirements carry the
provenance chain; existential lowering places definedness guards under
their binder as body conjuncts, since an implication there would be
vacuously satisfiable; loads through foreign static objects and
`loadable(p[a..b])` ranges over an external argument synthesize and
round-trip.

## Remaining gaps

Twelve fixtures have automatic proofs that rely on the hidden discharge:
`cstr_dynamic_indexed_read`, `cstr_dynamic_indexed_read_requires_permission`,
`cstr_dynamic_loadability`, `stdlib_external_contracts`,
`exists_loadable_range`, `forall_loadable_range`, `file_scope_static_arrays`,
`static_array_parity_scalar`, `static_array_parity_multidimensional`,
`static_array_parity_fixed_multidimensional`, `static_local_arrays`,
`contract_refinement_uses_implied_requirement`, plus `examples/bounded-pool`
and `examples/owned-string`. Their C and their proofs stay as they are; the
planner must close them. Two capabilities are missing, both supplied by
the deleted derivation leg:

1. **Planning a witness, a snapshot transport, and range coverage together.**
   The `cstr` family's remaining red requirement is
   `exists len. loadable(bytes[len..len + 1])` (with its definedness guard
   as a body conjunct). After `witness`, the body owes a loadability at the
   current point while the covering `loadable(bytes[0..len + 1])` sits at
   the caller's entry snapshot, across the caller's own local-declaration
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
existential over `CInt32`, pre-existing; and a `both` on a guard conjunct
leaves a body below it unrenderable when the written form cannot travel
with either arm, the conjunct-guard record the normalization planner lacks.

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
