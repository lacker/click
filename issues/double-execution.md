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

Proof-level `if` cases now retain a kernel-issued complementary partition at
the unchanged C frontier. Direct sealing requires both arms to be represented,
rejects duplicate decisions on one retained path, and checks each retained
path against its corresponding case decisions. A mid-execution two-arm proof
case therefore seals with zero whole-body executions. Terminal C joins retain
their already-aligned path traces.

Post-execution resource folds and nested opens now seal from the retained
transition theorems. A kernel-checked function-entry artifact retains the
exact population materialization and permits a rebased entry only when C
memory, heap lifetime state, local-object cells, resource meaning, and counted
populations remain definitionally equal. Composite resource relations are
derived once from that checked entry and may discharge only explicit resource
containment and separation premises. Regressions require zero whole-body
executions for a post-execution fold, nested composite-resource scopes, and an
explicit owned quantity; a negative kernel test rejects changed memory values
and changed population counts.

Pure and mixed pure/resource `branch ensuring` proofs can now retain one
checked interface branch event. The artifact validates both exact source-arm
traces, the exhaustive condition split, the deterministic abstract successor,
every state-parametric exported fact, and whole-context resource availability
in both arms. Its validated successor-fact delta becomes certified execution
evidence rather than a caller assumption, so a continuation may read an
abstracted local and use the interface fact to establish the function outcome.
Exact common non-scalar memory is preserved; differing memory still receives
the conservative havoc. Pure-result and owned-quantity regressions now seal
with zero whole-body executions, and kernel negatives reject an unproved
successor fact and a resource absent from both arms.

A quantified resource close after C execution remains on the fallback. That
operation can change an observed exit population used by an outcome predicate;
the checked entry artifact does not establish this exit transition. The guard
is now limited to quantified folds and closes rather than treating every
post-execution resource representation change as unsupported.

Likewise, a counted entry whose output resources are closed only implicitly by
outcome `simp()` remains on the fallback. An explicit checked `frame()` retains
the exit transition and seals directly; the implicit closer currently retains
only the finished claim proof, not equivalent execution evidence. The
`resource_count_patterns` mdtest pins this distinction.

Unsupported evidence shapes deliberately retain the old independent check for
now. Transformed resource interfaces with exports beyond the state-parametric
fact rule remain on the fallback, as do interface facts that require recorded
snapshot or proof-mark lowering. Outcome predicate unfolding, quantified
exit-population transitions, and implicit counted-resource closure are the
other explicit guards in claim finishing. Once these forms are typed evidence,
the fallback and its cache can be removed rather than weakened piecemeal.
The branch-interface resource projection and observation boundary is tracked
in [Make branch joins preserve explicit checked interfaces](branch-joins.md);
that issue owns the join-semantics cleanup rather than widening this migration
issue into a general branch redesign.

There is a second fallback at the opaque-contract boundary. Final contract
certification normally reuses the checked whole-body artifact created by claim
finishing, but it silently executes the body again when exact reuse,
resource-rebased reuse, or entry-partition reuse fails. Thus one proof can
perform its proof-directed statement execution, one independent claim
execution, and in a mismatch case another fresh contract execution. The
independent-execution cache reduces repeated work across claims but does not
remove this architecture.

This is why failures can report that proof construction succeeded but a later
execution could not reproduce it. The arena-shaped nested resource-scope
failure is now covered by a zero-rerun regression, and the `examples/arena`
project verifies. The intended `arena_write` contract is not currently present
in that sidecar, so the issue still requires the explicit end-to-end acceptance
regression below before completion.

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

Proof-level case partitions use the same exhaustiveness boundary. The kernel
issues one partition only for complementary facts rooted in the same checked
fact context and records each arm as a zero-source-advance execution event.
The sealer accepts a multi-case family only when every partition has both arms
and the artifact's case decisions correspond, modulo kernel-checked condition
polarity equivalence, to the candidate path decisions. It cannot accept an
arbitrary subset of candidate indexes merely because each selected path checks
independently.

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
