# Eliminate double execution

## Status

The first migration slice is complete. The proof object now retains the kernel
theorem for each checked statement and condition transition, and the kernel can
seal a complete trace, including nested shared-continuation branch evidence,
into the checked function execution consumed by claim and opaque-contract
certification without executing the C body again.
Deterministic regressions require zero whole-body executions for ordinary
grouped proofs, including a proof that carries an abstract resource predicate,
for explicit C branches whose arms return directly from the function, for a
bounded concretely stepped loop, and for a loop discharged by a verified loop
summary. Shared-continuation C joins now retain one kernel-checked nested event:
the split owns the exact source `if` and tail, both arm deltas descend from the
same persistent trace, and final sealing checks the two arms before resuming
the continuation once. Successive joins therefore do not multiply paths.

Unsupported evidence shapes deliberately retain the old independent check for
now. Terminal C joins retain their already-aligned path traces. The remaining
slices are proof-level case partitions, post-execution resource folds and
opens, and counted-population entry normalization. Once those are represented,
the fallback and its cache can be removed rather than weakened piecemeal.

There is a second fallback at the opaque-contract boundary. Final contract
certification normally reuses the checked whole-body artifact created by claim
finishing, but it silently executes the body again when exact reuse,
resource-rebased reuse, or entry-partition reuse fails. Thus one proof can
perform its proof-directed statement execution, one independent claim
execution, and in a mismatch case another fresh contract execution. The
independent-execution cache reduces repeated work across claims but does not
remove this architecture.

This is why failures can report that proof construction succeeded but a later
execution could not reproduce it. The arena write proof is the current
end-to-end example: scoped resource operations give the checked proof a valid
execution representation, while the later whole-function execution rebuilds a
different representation and fails before the claim can be certified.

## Violated invariant

A completed checked proof object must be the execution evidence for the
function it proved. Ordinary verification must not secretly execute the same C
body again to decide whether that proof object was valid. A mismatch in typed
evidence must be rejected at the operation that creates or composes that
evidence, not hidden by a fresh whole-body fallback.

Removing the later execution is a soundness-boundary change, not deletion of a
redundant call. Today `publish_checked_frontier_transition` explicitly leaves
semantic validity to its Surface caller, and the proof object throws away the
statement theorem that justified the transition. The replacement must retain
kernel-issued typed evidence through:

- sequential statement and condition transitions;
- explicit C branches and proof-level case partitions;
- verified and concretely executed loops;
- scoped resource opens, folds, unfolds, and equivalent ghost-resource
  representations;
- joins and complete function outcomes; and
- pure prerequisites used by an execution transition.

At function exit the kernel must seal that evidence directly into the checked
function execution consumed by claim and opaque-contract certification.
Contract certification may still check requirements, effects, postconditions,
path coverage, and opaque-rule eligibility; it must not rediscover the C
execution that established them.

## Related two-pass paths

The audit found two hidden whole-body rerun sites in ordinary verification,
both in scope for this issue:

1. `finish_ordered_proof` independently executes the function to replace its
   theorem-free execution candidates.
2. Final opaque-contract certification falls back to fresh body execution when
   a supplied checked artifact cannot be reused.

The following are intentionally separate operations and are not double
execution in this sense:

- `click expand` verifies the rewritten source artifact it emits;
- `click audit` cold-verifies original and rewritten artifacts for comparison;
- expansion regressions independently verify serialized proof text; and
- an opaque function call uses its installed rule without executing the
  callee body.

Smart-tactic search may try more than one checked successor before selecting
one, but ordinary verification does not currently run a mandatory second
per-tactic certification pass for the selected successor. Keep that property.

## Shared-continuation partition design

A nonterminal branch must not remain as a flat family of every path through
the rest of the function. Sequential two-way branches would otherwise grow
that family exponentially even when every branch immediately rejoins the same
state.

Instead, branch entry should retain one kernel-issued condition-partition
artifact tied to the exact checked fact context that created it. The artifact
records the complete feasible condition outcomes; Surface code cannot assemble
one from unrelated arm theorems. At the join, the kernel checks that:

- the artifact belongs to the unchanged branch-root fact context;
- every feasible outcome is represented exactly once by the matching arm;
- each arm's evidence is an append-only delta from the same parent trace;
- both deltas execute the selected source arm and reach the checked common
  successor; and
- no condition premise, arm path, or successor state is supplied only by
  Surface bookkeeping.

The result is one nested checked branch event appended to the parent trace,
not two live continuation paths. Later statements append once after that node.
Checking and storage are proportional to the evidence actually written in the
two arms, and sequential joined branches remain linear in the proof rather
than forming a Cartesian product.

The shared-continuation composition is implemented. Branch entry retains every
kernel condition path, including infeasible and error outcomes, and joins reject
a different state, condition, fact root, unmet path prerequisite, arm polarity,
theorem, or incomplete coverage. Both checked arm deltas are retained inside one
nested execution-evidence node, and final sealing consumes that node at the
common continuation without executing the C body.

Proof-level case partitions need the same exhaustiveness boundary. A sealer
must not accept an arbitrary subset of candidate indexes merely because each
selected path checks independently; it may select groups only through a
kernel-issued partition artifact proving that the groups collectively cover
the parent context.

## Intended regression

Add deterministic tests that reset the checked whole-function execution
counter, verify explicit proofs, and require claim and contract finalization to
perform zero whole-body executions after the proof object's statement
transitions. Cover at least:

- a straight-line function proved by explicit `step()` operations;
- a C `if` with both checked branches;
- a verified loop and a bounded concrete loop path;
- a scoped composite-resource mutation; and
- `examples/arena/arena_write.c` through nested `arena_region` and
  `arena_metadata` scopes.

Add negative kernel tests showing that an incomplete path, a mismatched
statement theorem, an unproved entry premise, a non-exhaustive branch family,
or an inequivalent ghost-resource transition is rejected without executing the
function as a fallback.

## Acceptance criteria

- The proof object retains typed kernel execution evidence instead of reducing
  completed paths to theorem-free `CFunctionExecutionCandidates`.
- A completed proof seals that evidence directly into the checked function
  execution used for its claims.
- Ordinary claim finishing contains no independent whole-function execution
  or independent-execution cache.
- Opaque-contract certification never silently executes a supplied proof's C
  body when its evidence is missing or mismatched; it reports the evidence
  error instead.
- Adding claims does not add executions, and explicit proof checking remains
  approximately linear in selected C, Click, and evidence size.
- The arena write contract keeps its narrow mutable footprint and verifies
  without new surface syntax or weakened resource semantics.
- Documentation no longer describes independent body execution as the normal
  certification model. It continues to describe `click expand` and
  `click audit` as independent artifact checks.
- `scripts/check.sh` passes.
