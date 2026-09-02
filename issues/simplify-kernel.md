# Remove search, fuel, and fallbacks from the kernel

## Status

Filed 2026-09-02 from a census of the kernel's reasoning routes over both
fixture harnesses (method below). The slices are listed in landing order;
each lands green on its own. Slice 1 landed on 2026-09-02 with one
exception: excluded middle in the certification prover stays until slice
2, because one surface unit test (`smart_fixed_state_have_if_retains_checked_arm_proofs_directly`)
closes an `or`-shaped ensure with `assumption()` and claim certification
does not match that completion, so the arm is what certifies it today.
Slice 2 is under way: completions are matched in one canonical form,
across rebased artifacts, and as a registered predicate's identity, and
the implicit closer records a completion, which took the second-proof
route from 320 claim paths to 28 over the harnesses. What remains is
structural: the proof lowers a claim goal through the surface's fixed-state
lowering, which resolves values through facts and names parameters with
its own symbols, while certification lowers the contract ensure through
the kernel, so some completions read `true` or name a surface symbol where
the kernel's lowering keeps the term. Closing the route needs one lowering
for both: the proof's claim goal as the kernel's lowering of the contract
ensure at the outcome state.

## Violated invariant

The kernel checks; it does not search. A kernel decision is simple: it is
decided by rules whose work is bounded by the inputs they name, it never
depends on a fuel counter or a depth cut, and it never tries a broader
route after a narrower one fails. Search belongs to the surface's smart
tactics, whose results are certificates the kernel then checks. The
double-execution and sealing removals established this for execution; the
proof object now validates each step as it is recorded. Reasoning inside
the kernel has not had the same pass, and the census shows the same two
shapes there: work done twice, and fallbacks standing in for a design.

What the kernel contains today:

1. **A general prover that searches.** `PureFactContext::proves`
   (`src/kernel/assumptions/proposition_reasoning.rs`) tries, in order:
   decision, a memory-DAG walk, deep canonicalization to depth 64,
   implication by assumption, finite-forall instantiation, a
   context-inconsistency check, a finite context split, and case splits
   over ambient disjunctions. Its decisions run under a 300-unit fuel
   (`DEFAULT_SIMP_REASONING_FUEL`, `src/kernel/assumptions.rs`) and under
   depth cuts (`MEMORY_LOAD_EQUALITY_DEPTH_LIMIT = 2`,
   `MAX_SIMP_FACT_REASONING_DEPTH = 8`, `SIGNED_INTERVAL_DEPTH_LIMIT = 32`).
   A `search_truncations` counter records every cut so memo layers can
   refuse to cache an answer whose search was cut short.
2. **A certification prover that searches.** `certification_proves_proposition`
   (`src/kernel/api/contract_certification.rs`) is a rule chain that
   branches on `or` by assuming a negation and retrying, instantiates
   quantified facts and recurses on their premises, hands predicates and
   everything unmatched to prover 1, and finishes with ambient disjunction
   cases. Four of its arms are switched off by the `CLICK_DISABLE_CERT_ARMS`
   environment variable, in production code. Its comments say the
   fuel-dependent decision procedure stays out of certification; two of its
   arms call it.
3. **More fuel.** `MEMORY_RESOLUTION_NODE_BUDGET = 8_000` and
   `RESOURCE_PROVER_NODE_BUDGET = 5_000`
   (`src/kernel/reasoning/memory_resolution.rs`),
   `MEMORY_DAG_HOP_DISTINCTNESS_FUEL = 128` (`src/kernel/memory_provenance.rs`),
   a constant-resolution step budget
   (`src/kernel/assumptions/condition_reasoning/decision.rs`), and a
   re-entry cycle cut on condition decisions.
4. **Ladders.** Five "exact route, then broader route" pairs that answer one
   question twice when the first route fails: resource satisfaction
   normalizes the context and retries (`src/kernel/primitives/resource_algebra.rs`);
   memory provenance tries targeted transport then a recursive solver
   (`src/kernel/memory_provenance.rs`); aliasing tries direct address
   arithmetic then separation certificates then a disjointness-fact scan
   (`src/kernel/assumptions/memory_reasoning.rs`); load equality tries the
   memory-DAG walk then canonicalization then equality facts
   (`src/kernel/reasoning/memory_resolution.rs`); loadability bounds retry at
   element granularity (`src/kernel/api/contract_certification.rs`).
5. **Two second passes of the double-execution kind.** Claim certification
   (`src/kernel/api/contract_certification/contract_claims.rs`) matches a
   claim against a recorded completion and, when none matches, lowers the
   ensure and proves it with prover 2. Only two closers record completions
   (`ClaimClosure::by_exact_check_completing` for `assumption` and
   `normalize` in `src/surface/proof/claim_proofs.rs`); every other closer
   leaves none, so its claim is proved a second time. And
   `prove_c_function_contract_execution_paths_with_checked_artifacts`
   (`src/kernel/api.rs`) still executes the body when a caller supplies no
   artifact (`ContractFallback::NoArtifact`); the corpus never takes it.
6. **Environment switches in production kernel code**: `CLICK_DISABLE_CERT_ARMS`,
   `CLICK_DISABLE_MEMORY_DAG`, `CLICK_DISABLE_DECIDE_MEMO`,
   `CLICK_CHECK_CANONICAL_AT_CREATION`, `CLICK_CHECK_CANONICAL_AT_CREATION_WIDTH`,
   `CLICK_DBG_SEP_PARITY`.

## Census

Measured 2026-09-02 on master `e569a022` with a temporary counter at each
route, incremented when that route was the one that decided (for ladders,
the layer that returned true; for provers, the arm that returned true) or
when a fuel or depth bound was hit; both harnesses run once, the examples
also per project. The instrumentation is not landed; it is a dozen
`record_reasoning_route("...")` calls at the sites named above, printed by
the harnesses after the run, and takes an hour to reapply. Counts are
examples / mdtests.

Load-bearing:

- Claims certified by completion match: 199 / 403. Claims proved by
  prover 2 instead: 179 / 141, which is a third of all claim paths. Almost
  every such claim had no completion recorded at all (`simp`, `frame`, and
  default closers); a few had one that did not match (`or`-shaped ensures,
  `vector_grow`). Registered predicate ensures: 5 / 14.
- Prover 1 deciding inside prover 2: 127 / 72, by proposition kind:
  resource separation 80, universal facts 68, implications 38, resource
  composition 10, negation 2, loadability 1.
- Memory-resolution fuel exhausted: 85,001 / 5, of which perpetual-service
  83,526 (a 124-line example verified in 2.3 s), owned-vector 996,
  owned-string 229, binary-tree 199, arena 37. Simp fuel exhausted:
  1,023 / 1,672, all of the examples' share in owned-vector. Resource-prover
  fuel: never.
- Load-equality depth limit hit: 765,954 / 341,132 (perpetual-service
  379,893; owned-vector 271,992; owned-segmented-buffer 78,548;
  owned-string 33,324). Every hit marks the enclosing decision as truncated,
  which the memo layers treat as uncacheable, so the same negative answers
  are recomputed. Condition-decision cycle cuts: 7,875 / 1,919.
  Constant-resolution budget: 317 / 0.
- Ladders: load equality decided by the DAG walk 22 / 26, by
  canonicalization 105 / 1,490, by equality facts 14,183 / 768, so the first
  layer is a failed attempt on nearly every query. Resource normalization
  retry 42 / 3. Alias separation certificates 2,116 / 17. Loadability
  element retry 0 / 2.
- Prover 1's own broader routes: finite-forall instantiation 0 / 48,
  finite context split 0 / 20, inconsistency 13 / 5. Prover 2's
  alpha-equivalent quantified fact 1 / 8, quantified condition
  instantiation 0 / 2.

Never decided anything over the corpus (nine routes):

- prover 2: excluded middle on a disjunction; ambient disjunction cases;
  the canonicalized-load retry; prover 1 on a predicate; a predicate from a
  quantified implication;
- prover 1: disjunction cases;
- memory provenance: the recursive solver after targeted transport;
- aliasing: the disjointness-fact scan after the certificates;
- resource-prover fuel exhaustion.

## Intended regression

Kernel unit tests that a route deleted here no longer exists and that its
callers decide by the remaining exact rules; a surface test that every
claim closer records a completion and that claim certification is a match
against it, never a second proof; the fixture harnesses with the
contract-fallback census still pinned at zero and no `NoArtifact` route to
count; and, for every fuel or depth bound replaced, a deterministic scaling
regression over several input sizes showing the replacement's work is
bounded by its inputs (`docs/internals/verification-efficiency.md`).

## Slices

Each slice is one worktree, one green `scripts/check.sh`, one fast-forward.
Take a fresh census with temporary counters at the start of any slice that
depends on a count.

1. **Delete the dead routes** listed above, with the tests that exist
   only to exercise them. Where a route is the only caller of a helper,
   delete the helper. Done for eight of the nine; excluded middle waits
   for slice 2 (see Status).
2. **Every closer records a completion.** Extend `ClaimClosure::by_exact_check_completing`
   to `simp`, `frame`, and the default closers, so claim certification
   matches every claim. Drive the "proved by prover 2" count to zero with a
   temporary census, then delete the second-proof route
   (`certification_proves_post_proposition` and the ensure re-lowering
   around it).
3. **Delete artifact-less body execution** from
   `prove_c_function_contract_execution_paths_with_checked_artifacts` and
   `ContractFallback::NoArtifact`; a caller with no artifact gets no paths
   and the reason, as one with an unusable artifact already does.
4. **Move the environment switches out of the kernel**: each becomes a
   test-only configuration or is deleted with the route it switched.
5. **Replace the ladders whose first layer rarely decides** with the
   deciding layer alone, or reorder so the deciding layer runs first, each
   under a count from a fresh census: load equality first, then memory
   provenance and aliasing.
6. **Prover 1 out of certification.** Replace the two `assumptions.proves`
   arms of prover 2 with exact rules for the four kinds the census saw
   (resource separation, universal facts, implications, resource
   composition), then delete the handoff.
7. **Remove the fuel.** For each bound, in the order resource prover
   (never exhausted), memory-DAG hop, constant resolution, simp reasoning,
   memory resolution, load-equality depth: replace the count with a
   structural bound proportional to the query's inputs (a cycle check on
   the query rather than a depth, an index rather than a scan), prove it
   with a scaling regression, and delete the counter. The load-equality
   depth limit of two, hit a million times, is the design problem of this
   list: a recursion that exceeds its own bound on nearly every query and
   defeats memoization each time. When no bound remains, delete
   `search_truncations` and the memo gating that reads it.

## Not in scope

- Smart tactics and search in the surface; they produce certificates the
  kernel checks, which is where search belongs.
- The open kernel-API soundness issues (`kernel-binder-hygiene.md`,
  `contract-rule-trust-boundary.md`, `call-havoc-fingerprint-collision.md`,
  `kernel-hardening-batch.md`); they are filed separately and may land in
  any order with this.
- Performance work on rules that are already exact.

## Acceptance criteria

- No fuel counter, depth cut, or `search_truncations` under `src/kernel/`;
  every bounded rule's bound is a function of the inputs it names, with a
  scaling regression.
- Certification decides by matching recorded completions and by exact
  rules; `PureFactContext::proves` is not called from
  `src/kernel/api/contract_certification/`, and no kernel rule issues a
  theorem by search.
- No route in the kernel tries a broader method after a narrower one fails
  on the same question.
- No `std::env` read under `src/kernel/`.
- Both fixture harnesses pass with the contract-fallback census at zero;
  harness times do not rise.
