# Finish the remaining proof-driver migration

## Priority and relationship to arena work

P1 proof-driver migration and tooling correctness. The legacy execution and
fallback paths keep causing inconsistent proof behavior and can make ordinary
verification disagree with the checked proof boundary, so this cleanup is
required before launch. It is not a prerequisite for resuming [arena
ownership](arena-resource-ownership.md): the targeted arena prover repairs have
landed—resource/invariant fact correspondence, exact premise presentation, the
non-progressing atomic extraction retry, mid-execution `have`, and the direct
increment-bound lookup. Do not duplicate those fixes here. The remaining
symbolic allocation proof belongs to the arena issue.

The work packages below are sequential green
commits, not a request to rewrite the entire verifier at once. If one of these
paths independently exhibits a tooling failure, the affected work becomes a
blocker under `AGENTS.md`; that does not promote every cleanup package.

Reviewed against `092c8599`. The earlier broad proposal remains available at
`ad691bd9:issues/prover-bugs.md`. The inventory below replaces its instruction
to search for and delete everything called legacy. It identifies actual
runtime paths, not just comments or naming conventions.

## Violated architectural invariant

For supported source proofs, one checked operation pipeline must own evolving
semantic state, completion evidence, and the provenance of successful steps.
A driver must not interpret the source a second time because the first driver
rejected it, or rebuild a working fact vector to recover that driver's state.
Presentation certificates describe checked operations; a syntactically valid
certificate alone is not a witness that a claim was proved.

Independent verification of emitted Surface Click is intentionally retained.
Parsing/lowering an independently checked expanded proof is not an illicit
second authority. Bounded alternative search strategies are also legitimate
when every success is a checked descendant of the same input proof.

## Decisions already made

- Extend the existing persistent `Proof` API. Do not introduce a second proof
  IR, new public certificate grammar, or global fact-ID migration.
- Keep the kernel/language split: kernel rules validate semantic transitions;
  language code resolves names, plans tactics, and renders provenance.
- Perform migration by source operation and caller, preserve existing accepted
  explicit scripts, and delete the replaced implementation in the same chunk.
  Making a new route preferred while leaving the old one callable is not done.
- An explicit operation's error must propagate. A supported script ending with
  an open goal is an ordinary proof failure. An unsupported operation must have
  a specific diagnostic, not be tried in a different interpreter.
- Smart planning can return a bounded miss. Port a needed existing strategy
  into planning over checked operations; do not preserve its separate semantic
  executor or require global search completeness.
- Match/refold can change what an unqualified model expression denotes. Keep
  checked historical anchoring and memory transport. Do not replace them with
  arbitrary source-text-to-fact aliases.
- Do not broaden whole-contract theorem authority to new binder types as an
  incidental cleanup. The current int32-only authority boundary and checked
  structural-induction rules must remain explicit until a separately justified
  extension changes them.

## Inventory and work package A: pure theorem compatibility interpreter

Primary file: `src/surface/proof/pure_theorems.rs`.

Package A is complete. Ordinary pure defaults, smart scripts, explicit scripts,
branch continuations, nested `have` bodies, and numeric induction now finish on
an authoritative `Proof`. Checked operation failures propagate with the actual
focused goal, source position, and bounded search context. Unsupported operations
name the operation. No pure caller reruns the source to recover a diagnostic.

The old mutable pure interpreter and its prove/build/validate entry points are
removed, together with the compatibility dispatch predicate and their unused
planning/lowering helpers. Production pure acceptance no longer calls
`simp_proposition`; that helper remains only in diagnostic unit tests.

Numeric induction applies the existing checked induction operations. Smart
hypothesis applications prove their domain and substituted requirements in
checked `have` scopes against retained facts. Arithmetic planning selects signed
bounds through the goal variables' persistent index. Induction entry checks an
exact nonnegative domain, including a stronger constant lower bound. Applications
that close a goal before a later source step retain their checked descendant as
a `have`, without executing its serialized steps again.

Pure theorem results retain their checked proposition completion. Structural
induction remains a distinct checked rule: constructor coverage and descent are
checked, and each arm's completion is retained through serialization. This adds
no whole-contract authority for algebraic or Integer parameter binders; the
existing int32 authority boundary remains unchanged.

The shared checked planners now cover the previously hidden pure strategies:
selected facts exposed by predicate unfold, constructor-field extraction and
contradiction, sequence conjunctions, Integer theorem requirements, and numeric
induction side conditions. Source `have` bodies may use checked smart tactics;
a search miss reports the actual nested operation instead of the old interpreter's
certificate-syntax refusal.

The universal-instantiation slice remains on the same shared `InstantiateUsing`
operation in pure, fixed-state, and execution contexts. Argument capture retains
introduced names and shadowing; indexed fact availability and named guards are
checked by the kernel. Pure `assumption` recognizes indexed alpha-equivalent
quantified facts.

Regressions cover ordinary explicit/smart completion, numeric induction expansion
and independent reverification, distinct structural arm evidence, negative source
operations, and narrow source boundaries against the removed pure APIs. Expansion
still independently verifies the emitted Surface Click.

Implemented instantiation regression:

```click
theorem instantiate_bound(x: int32, limit: int32, upper: int32) {
    requires forall (k: int32) {
        0 <= k and k < limit implies k <= upper
    };
    requires 0 <= x;
    requires x < limit;
    ensures x <= upper by {
        instantiate(forall (k: int32) {
            0 <= k and k < limit implies k <= upper
        }, x) using { 0 <= x; x < limit; }
        assumption();
    }
}
```

The regression now checks retained `kernel_authority`, checked instantiation
provenance, and the absence of ordinary certificate-construction/validation
reruns. It covers missing and unavailable guards, an unrelated open goal,
introduced and nested shadowing binders (including Integer/int32 shadowing),
numeric induction, and smart-caller expansion/reverification. The shared checked
script driver also carries `if`/`cases` continuations into each checked arm;
regressions retain both arm certificates and reject wrong-sibling evidence. The premises are jointly satisfiable (for example,
x = 1, limit = 8, upper = 10). A deterministic 8/16/32/64 regression checks
persistent allocations while unrelated facts and theorem bindings grow.
These tests and the existing numeric/structural induction, Integer, generic
theorem, and constructor-coverage negatives remain part of the gate.

## Inventory and work package B: explicit error-to-compatibility conversion

Package B is complete. Source scripts in the remaining execution scopes,
outcome `have` bodies, and fixed-state planning callers now use the same
propagating `Proof` driver as pure theorems. Nested scopes and branch arms
inherit that behavior. Unsupported operations name the written tactic;
explicit failures retain their diagnostic, and open source goals fail.

Removed `try_linear_script`, the generated-script entry point and driver-mode
flags, whole-script capability prechecks, and the explicit fallback counter
and counting helper. Outcome haves no longer retry a declined source body as
generated code. Fixed-state source scripts no longer fall through to unchecked
certificate construction.

Smart planning remains distinct from source execution. A selected atomic plan
is checked on its input Proof and its refusal is classified through `attempt`.
The loop smart closer selects ordinary simplification or its existing bundle
member planner directly on the same root; it does not run a source script and
reinterpret its error. Explicit loop closure bodies propagate their errors.

A completed theorem application followed by more written steps retains its
checked descendant as a fact in pure and fixed-state/execution contexts.
Retention verifies context, branch, ancestry, and source-to-kernel goal
correspondence; it does not reopen the body or execute its certificate.

Existing expansion, tampering, sibling-isolation, and no-body-rerun regressions
remain. Counter assertions were removed while retaining their behavioral
checks; additional assertions check retained proposition completion and
provenance. Regressions cover source failures before and after execution,
unsupported operations, named theorem failures, source error versus deliberate
candidate refusal, and 8/16/32/64 fact-sharing during completion retention.
Narrow source-boundary tests prevent the deleted entry points from returning.

The remaining outcome adapters and loop-initialization layout/certificate
orchestration below remain separate work packages.

## Inventory and work package C: outcome drain and resource fact adapters

Package C is complete. The post-execution drain now reads the focused outcome
Proof's persistent facts. Haves, predicate unfolds, transport, composite folds,
open-scope closure, and contract resource effects advance their checked
successor. Smart grouped closure retains its resulting Proof as well as each
claim completion. No caller reconstructs or reinstalls an ambient fact vector.

Source requirement correspondence is built from immutable entry origins, not
the prefix of evolving facts. Resource projection and scope closure use the
persistent resource adapter. Fold invariants are lowered against the current
outcome; historical spelling alone cannot reuse an entry-era invariant after
its population changes. Existing checked effect matching transports earlier
evidence, without rebuilding a path-wide assumption context per fold. Checked
64-bit equality uses its existing indexed constant-equality component, including
call postconditions; unrelated facts are not scanned. Store consequences are
checked once per outcome and retained with that outcome. Retained proposition scopes may refresh only
from their owning outcome, preserving context, outcome identity, and result.
That outcome identity survives existential scopes' local branch IDs. Entry and
resource premises with different snapshot spellings are paired by their checked
kernel endpoint, then validated by the ordinary named-premise operation.

Removed `LegacyResourcePureFacts`, its observation/fold/vector wrappers,
`with_checked_outcome_facts`, `resync_ordered_preserving_provenance`, and the
drain's fresh fixed-state fallback roots. Borrowed premise views reuse the
persistent assumption and exact-fact indexes. Output-sized certificate vectors
and bounded smart-search candidate exports remain explicit boundaries.

Claim closure separates presentation from evidence. Proposition claims require
`CheckedProposition`, including exceptional outcomes; exact resource production
returns an opaque witness tied to the checked execution, path, and claim key; vacuity is read from the checked
execution theorem. Proof-produced execution paths retain the checked body-to-exit
outcome correspondence, including aggregate return layout restoration, so
completion binding checks its exact producer without comparing away memory
changes. Generic certificate-only and empty exact-check constructors are gone. Grouped closure associates each claim with its evidence, and final
assembly rejects missing, mismatched, or wrong-path evidence. Independent
contract certification still validates the checked execution and entry premises.

Regressions cover mixed scalar/resource grouped claims, a fold on only one
returning branch, distinct sibling results, divergent paths, evidence identity,
and expansion/reverification with result tampering. Deterministic 8/16/32/64
curves vary unrelated facts and repeated post-execution haves/folds independently:
checked operations materialize no ambient facts, and end-to-end incremental
indexing/export work depends on the produced deltas rather than ambient size.
Existing resource-scope, predicate-provenance, wrong-sibling, and no-body-rerun
regressions remain in the full gate.

## Inventory and work package D: loop-initialization certificate gateway

The producer prerequisite is implemented: `kernel::c_loop_entry_goals` keeps
exact entry judgments and lowering metadata grouped by declaration, including
satisfied and duplicate declarations. Path facts and loadability conditions
remain guards on those judgments. The existing outstanding-obligation query
still serves the current initialization driver until its migration lands.

The nested-loop clause ownership prerequisite is also implemented. Frontier
binding replaces the previously registered clause for the same C loop identity,
including its proof-local scope, while retaining separate invariant declarations
within that clause. The nested-loop regression verifies and expands twice; the
binding regression checks scope replacement and preservation of duplicate
invariant spellings. This prevents two written inner invariants from producing
four lowered checks when the outer proof already registered the inner clause.

`execution_planning/loop_planning.rs` recognizes an expanded source layout of
helper steps followed by one `have` per invariant. It specially dispatches
`source_contains_legacy_arithmetic` and uses
`pure_goal_proof_certificate_gateway_with_checked_result` to plan a certificate
and sometimes check it again. This is an orchestration duplication, not
permission to delete the source `arithmetic() using` operation.

Parse the initialization layout once. Run helpers once in source order on a
retained initialization Proof, then check each declared invariant against its
exact producer-owned entry obligation. Ordinary explicit bodies apply checked
steps directly. Source arithmetic requests plan their selected explicit
certificate on that same proof; generated `ArithmeticCertificate` steps check
without search. Preserve the distinction between a shared initialization body
and separate per-invariant bodies.

Retain the checked completions and attributed provenance, removing the special
arithmetic compatibility branch and the redundant certificate-validation path.
Once A and D remove their ordinary-verification callers, delete the two generic
`pure_goal_proof_certificate_gateway*` helpers from `src/surface/proof.rs`.
Keep the independent expansion verifier; do not transplant the helpers into a
new hidden checker.

Tests: two invariants with one preceding helper have, mixed explicit/arithmetic
bodies, duplicate invariant spellings with distinct clause positions, and
expanding then re-expanding initialization. The helper must execute once, not
once per invariant; the expanded proof must be a fixed point and must not
multiply sibling proof bodies. This package does not redo the already-landed
preservation fact-correspondence repair.

## Inventory and work package E: misleading counters and documentation

`src/instrumentation.rs::ContractFallback`, `BodyRerunCensus`, and associated
functions are misleadingly named. At the reviewed head,
`src/kernel/api.rs` records them when no checked execution artifact can be
reused, returns no paths, and emits a diagnostic. It does not run the body
again. Both fixture baselines are empty.

Keep the rejection diagnostics and regression signal. Rename these types,
functions, event labels, and fixture baseline names to describe artifact reuse
rejection; update messages claiming that a body was rerun. Update
`tests/{mdtests,examples}.rs`, instrumentation tests, and
`docs/internals/proof-objects.md`. This naming correction is an explicit
exception to “delete, do not rename”: this code is observation, not an old
semantic engine in disguise.

Likewise correct stale “legacy cursor wrapper above” and similar comments when
the referenced wrapper no longer exists. Documentation must describe actual
remaining boundaries rather than claiming that migration is already complete.

## Explicit exclusions: machinery that stays

Do not expand the inventory by substring search. These are legitimate unless
a separately demonstrated defect identifies a specific call path:

- independent parse/lower/check of expanded Surface Click;
- bounded smart planners that apply ordinary checked operations;
- resource validity, loadability, entry-premise authorization, and exact
  contract-exit checking;
- checked memory transport and current/old/at presentation validation;
- output-sized clause/certificate vectors and bounded diagnostic snapshots;
- conservative secondary resource indexes, including symbolic/block lookup
  fallbacks in `kernel/functions.rs`;
- `surface_synthesis` alternatives whose output is checked against the exact
  selected proposition. They generate presentation candidates, not facts;
- specialized checked arithmetic axioms and the existing structural-induction
  rule. Neither is a compatibility interpreter just because it has a separate
  implementation.

There is no requirement to remove every occurrence of `legacy`, `fallback`,
`Vec<Proposition>`, or lowering. Replace the enumerated semantic duplicates and
ambient rebuilds; do not change terminology to disguise a surviving one.

## Validation and acceptance

For each package, preserve acceptance of existing explicit proofs, retain
negative and tampering coverage, run focused tests and `scripts/check.sh`, and
integrate only a green commit. Performance changes need deterministic scaling
curves over several input sizes. Do not use a faster corpus run as their only
evidence. Positive proof changes also need selected expansion, independent
reverification, and audit coverage under the ordinary bounds.

Completion requires:

- A/B: ordinary pure proofs use the shared checked operations; the old mutable
  pure interpreter, compatibility dispatch, diagnostic reruns, and explicit
  error-swallowing fallback are deleted.
- C: outcome semantic state has one persistent owner; generic certificate-only
  claim closure and the enumerated vector/resync adapters are replaced by
  checked evidence and removed.
- D: loop initialization uses retained checked results without the special
  arithmetic certificate dispatch or ordinary-verification gateway recheck.
- E: reuse-rejection instrumentation remains accurate and useful, with corrected
  names/messages; documentation lists real special rules and authority limits.
- Tests prevent the specific removed APIs/alternate authoritative call paths
  from returning, while valid expansion and bounded planning remain supported.
- The previously fixed arena regressions still verify, expand, and audit;
  `scripts/check.sh` passes.

Mark these inventory packages complete as code and tests land. Delete this
issue and its README entry when all are done. Do not close it because counters
happen to read zero, and do not keep the removed engines dormant for difficult
cases.
