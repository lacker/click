# while-invariant rule: single-fork preservation check

Status: done (fenced) — worktree-agent-a15e77f5ef694f71f 2026-07-30
Claimed:

Scope (design-review honorable mention): the while-invariant rule
checks preservation in only one condition-fork context and against
pre-body state (old api.rs:2633; re-locate). Currently exercised only
by tests but exported. Either fix the rule to check both fork contexts
against the right state, or fence it (unexport / doc-comment the
limitation) so nothing user-facing can rely on it.

Done when: the rule is sound or unexported, with a kernel test pinning
whichever behavior is chosen; gates green.

## Outcome: option (b), fenced

`prove_c_while_invariant_rule` (was `pub fn`, api.rs ~5788) is now
`#[cfg(test)] pub(super) fn`, with a doc comment enumerating exactly what
it checks and what it does not. `condition_contexts_for_truthiness`
(reasoning.rs:95) was the rule's only caller, so it is `#[cfg(test)]` too;
without that the lib build gains a dead-code warning.

The rule had no callers outside `src/kernel/tests.rs`. `Theorem::new` is
`pub(super)`, so fencing the constructor makes
`Proposition::CWhileInvariantRule` unconstructible as a theorem from
outside the kernel. The `Proposition` variant and its traversal arms in
reasoning.rs / checking.rs were left alone.

### Defects found (all four, in the one function)

1. `.any()` over condition-true fork contexts: one fork establishing
   `preserved` is enough; a fork that breaks the invariant is skipped.
2. `.any()` over condition-false fork contexts for the exit: same, for
   `postcondition`.
3. The body's post-state is matched as `CStatementOutcome::Normal(_)` and
   discarded. `preserved` is caller-supplied and discharged against the
   *pre-body* assumption context, so nothing ties it to what the body
   does. This is the decisive one.
4. No havoc of loop-modified locations: preservation is shown for one step
   out of the caller's specific `state`, so it generalizes to an arbitrary
   iteration only if the caller happens to pass a fully generic state and
   assumptions. The rule does not check that.

Note the design review's "against pre-body state" is slightly off as
stated: `Assumptions` are state-free, so discharging against pre-body
assumptions is not itself the bug. The bug is (3) — the post-state is
never consulted at all.

### Why not option (a)

Fixing (1) and (2) is a two-word `any` -> `all` change. Fixing (3) is not:
"the invariant holds at the post-state" cannot be expressed when the
invariant is a flat `Vec<Proposition>` over raw symbolic terms. Relating
it to the post-state needs a substitution from each local's pre-value to
its post-value, which is only well defined when every pre-value is a
distinct bare `Variable` and the invariant touches no memory snapshot —
and any restriction strict enough to be sound also rejects ordinary
loops. The correct representation already exists: `CLoopInvariantCheck`
carries a state-parametric `SpecProposition` that the production path
evaluates at entry and at the back edge
(`c_loop_preservation_contexts` / `c_loop_invariants_hold_at_back_edge`,
with `prepare_loop_top_state` supplying the havoc for (4)). So a real fix
means re-basing the rule on `CLoopInvariantCheck`, which changes the shape
of `Proposition::CWhileInvariantRule` and duplicates machinery that
already works — a redesign, for a rule with zero callers. A partial fix
(1)+(2) was deliberately skipped: it would leave the rule unsound while
making it look audited.

### Tests

- `while_invariant_rule_ignores_what_the_body_does_to_the_invariant` —
  the same `preserved` list (describing `i := i + 1`) is accepted for a
  body that increments `i` and for a body that sets `i` to 0, pinning
  defect (3). Must start failing if the rule ever learns to check the
  post-state.
- `while_invariant_rule_is_not_exported_from_the_kernel` — `include_str!`
  guard on the `#[cfg(test)] pub(super) fn` declaration, so re-exporting
  the rule fails the gate.

### Gates

All three green; no corpus loop changed behavior (the rule was never on
the verification path).
