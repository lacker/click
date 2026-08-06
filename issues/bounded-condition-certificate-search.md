# Keep condition-certificate search bounded and diagnosable

## Problem

While restoring the general `vector_push` call in the owned-vector pipeline,
`execute_until(statement(4))` spends its smart-tactic allowance trying to
reconstruct one non-derivable equality from a wide ambient condition context.
The slow path is certificate-premise search, not C execution.

Certificate-reconstruction failures now summarize proposition kinds and bound
the number of unspellable premises instead of dumping kernel `CMemory` terms.
The remaining work in this issue is the bounded non-derivable-search regression
and its focused decomposition guidance, not general diagnostic serialization.

This is not, by itself, a requirement that `execute_until` find the proof.
Smart tactics are heuristic and incomplete. A difficult execution proof may
need to be decomposed into smaller smart operations or written as explicit
simple `step() using`, `derive using`, transport, and resource tactics. Click
must support that escape path; it must not continually retune global search
heuristics whenever one large smart tactic fails.

The tooling concern is narrower. One speculative internal condition can
consume essentially the whole outer smart-tactic budget, and the resulting
failure does not clearly identify the condition or recommend proof
decomposition. Earlier behavior also depended on the first 48 ambient facts
and tried every singleton and pair. Such heuristics may be incomplete, but
their cost, ordering sensitivity, and failure mode must remain bounded and
understandable.

## Non-goal

Do not make condition-certificate search complete. In particular, this issue
does not require the owned-vector proof to succeed as one
`execute_until(statement(4))`, nor does it require automatic discovery of every
derivation available from the ambient context.

Do not change global heuristics merely to make the current vector proof pass.
A heuristic change needs independent evidence that it improves a common proof
shape without destabilizing established cases.

## Violated invariant

An unsuccessful smart search is an ordinary proof-development result. It must
fail within its local budget, preserve a concise diagnostic identifying the
failed search obligation, and leave the user a supported route to continue
with smaller or simple tactics.

It becomes a tooling bug when search ignores or badly overshoots its budget,
emits an enormous or misleading diagnostic, behaves nondeterministically, or
the same obligation cannot be stated and checked through Click's simple proof
surface.

## Intended regressions

Add a small unit fixture containing many irrelevant condition facts, a wide
snapshot term, and a requested equality that the configured smart search does
not derive. It must stop at its local bound and report a summarized target and
search stage without printing the embedded memory state.

Add a companion proof that supplies the relevant intermediate fact or exact
premises explicitly and completes using simple tactics. This is the important
completeness boundary: automation may miss, while the proof language remains
capable of expressing the proof.

Keep a representative derivable multi-premise condition as a search-quality
benchmark, not as a promise that every fact ordering or arbitrarily large
context will be solved automatically.

The source-faithful owned-vector pipeline remains useful as an integration
case, but it may replace the broad `execute_until` with independently
comprehensible explicit steps. It must not change its C or add irrelevant proof
facts merely to steer search.

## Design direction

First make the existing search boundary and diagnostic precise. Charge nested
condition planning to the active smart tactic, stop cooperatively at the local
limit, and report the requested proposition, the proof site, and the fact that
the user can split the execution or provide exact premises.

Relevance-directed dependency slicing remains a possible general optimization:
equality and order facts whose operands connect transitively to the goal are
better candidates than an arbitrary prefix or all pairs. Snapshot lookup may
similarly follow the memory-derivation DAG by loaded address. Implement such an
optimization only with corpus-wide before/after measurements and expansion
regressions. It is not an acceptance requirement for this issue and must not
trade one collection of passing smart proofs for another.

Do not address the problem by raising time limits, changing C, adding magic
fact-count or term-count cutoffs to force the vector case through, or treating
eventual smart-search success as necessary.

## Acceptance criteria

- A non-derivable condition over a wide snapshot stops within the smart
  tactic's local budget.
- Its normal diagnostic identifies and summarizes the failed obligation,
  recommends decomposition or exact premises, and does not dump the full
  memory state.
- The companion explicit proof verifies using supported simple tactics.
- The owned-vector work is not blocked merely because one broad
  `execute_until` cannot find its complete proof.
- Any search-heuristic change is supported by a general benchmark and does not
  regress established verification, expansion, or replay fixtures.
- Search success, when it occurs, still produces the exact premises required
  by a replayable certificate.
- Profile, audit, and the default test suite pass within their normal budgets.
