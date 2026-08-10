# Retire the surface builder's remaining ambient threading

The expansion re-architecture this issue originally tracked has landed:

- every replayed tactic constructs its surface steps in a scoped builder, so
  its expansion exists as a standalone value (`begin_tactic_surface_scope`);
- expansion requests are an explicit `ExpansionCapture` threaded down the
  verification call stack, filled in as verification proceeds, and read after
  one ordinary verification run;
- the `TACTIC_EXPANSION_PROBE` and `SUPPRESS_TACTIC_EXPANSION_CAPTURE`
  thread-locals, the `ClickError::expansion_complete` sentinel and its
  abort-by-error protocol, and the mid-replay builder resets are gone.

What remains is the last piece of ambient state from the old design:
`SimpleProofBuilder` still lives inside `TacticReplayState`, and the deferred
bookkeeping (`DeferredTacticCapture`, `deferred_expansion_path_choices`)
rides along with it.

## Remaining work

- Pass the surface builder explicitly where proofs are built instead of
  carrying it in every cloned replay state. The tactic scope mechanism
  already isolates per-tactic construction; the builder itself could live in
  the replay driver rather than the state.
- Fold `DeferredTacticCapture` into the deferred post-execution record it
  shadows (`post_execution_tactics` already carries tactic and source
  indices), and consider making `deferred_expansion_path_choices` part of the
  typed branch path rather than capture-only state.
- `SimpleProofBuilder::lowering_planned_transition` is a re-entrancy flag for
  the statement-step constructor; a constructor argument would say the same
  thing without builder state.

## Constraints

Two invariants from the search-construction migration still bind here, with
regression coverage in the ordinary suite:

- Premises are spelled against `SimpleProofBuilder::certificate_facts` (the
  replay-visible fact set), not the planning executor's automatically
  transported facts
  (`expanded_branch_certificate_uses_the_branch_entry_state`).
- Construction sees program points as they stood before the current
  statement's entry recordings (`apply_construction_point_view`,
  `resource_neutral_callee_preserves_callers_allocation_resource`).

## Acceptance criteria

- `TacticReplayState` no longer carries a `SimpleProofBuilder`.
- Expansion output on the existing corpus (`lang::click::expansion::tests`)
  is unchanged.
