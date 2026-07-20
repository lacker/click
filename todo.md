# `click-expand` Handoff

## Objective

Finish `click-expand` so that every successfully verified, independently
selectable C claim proof can be replaced by canonical Click source containing
only simple tactics and control-flow tactics, and the rewritten sidecar verifies
the same specification. A selectable proof is one non-grouped ensure, one
non-grouped effect, or one grouped function proof. Every smart tactic reached
inside that selected proof is part of this requirement.

The intended invariant is:

> A smart tactic is search or orchestration over externally expressible simple
> tactics. Successful automation must produce a checked, replayable surface
> certificate. There must not be a second class of internal-only simple tactics.

This document covers the remaining work for that claim-source boundary. Pure
theorem proofs, loop `initialize`/`preserve` proofs, and structural-item proofs
also use the tactic language, but `CProofClaim` cannot select or rewrite them.
They are a follow-up source-expansion boundary and must not be included in a
claim that `click-expand` covers every proof-bearing construct in Click.

The certificate foundation, printer, public API, and initial CLI already exist.

## Accepted Scope

These are deliberate properties of the current tool, not TODOs:

- Expand one selected C function proof unit at a time: an ensure, an effect, or
  a grouped proof.
- Print the complete rewritten sidecar to standard output.
- Allow expansion itself to be slower than replaying expanded source.
- Keep `click-expand` as a separate binary rather than a proof-language tactic.

Do not add expand-all, in-place editing, certificate caching, or formatting
options until the correctness and corpus audit below are complete.

## Current Implementation

### User-facing command

```text
click-expand <sidecar.click> <function> <ensure:N|effect:N|grouped>
```

The command:

1. Reads the Click sidecar.
2. Resolves its `verifying` C files relative to the sidecar.
3. Verifies the original sidecar.
4. Selects one ensure, effect, or grouped proof.
5. Obtains and validates its surface tactic certificate.
6. Replaces the selected source proof.
7. Prints the complete rewritten sidecar to stdout.

The implementation currently verifies the original sidecar and validates the
certificate, but it does not re-verify the rewritten sidecar before returning
it. The round-trip check below should become part of the production source API,
not remain only a test property.

Claim indices are zero-based.

### Public Rust API

The source API is in `src/lang/click/expansion.rs`:

```rust
pub enum CProofClaim {
    Ensure(usize),
    Effect(usize),
    Grouped,
}

pub fn verifying_source_paths(click_source: &str) -> Result<Vec<String>, ClickError>;

pub fn expand_c0_claim_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError>;
```

Each `VerifiedCTheorem` exposes:

- `expanded_proof_tactics()`
- `expansion_blocker()`
- `expanded_proof_certificate()`
- `expanded_proof_source()`

`expanded_proof_source()` validates the certificate before printing it. An
unsupported item must produce an expansion blocker; it must never emit a
partial expansion.

### Certificate model

- `ProofReplayPlan` is private evidence used while planning or checking smart
  tactics. It is not surface Click and cannot appear in a certificate.
- `TacticCertificate` recursively permits only externally expressible simple
  tactics and supported control-flow nodes.
- The printer emits canonical, parseable `by { ... }` source.
- Proposition spellings are checked by lowering them back to the exact kernel
  proposition at the exact proof point. This is required because memory facts
  are snapshot-sensitive.
- Certificate replay starts from ordinary proof inputs and invokes the simple
  tactic executor. It must not rely on hidden state retained from smart tactic
  planning.

The relevant foundation was added in commits `8dc5002` through `cb27d3a`.

## Required Work

Do the following in order. Keep each conceptual fix in a separate commit.

### 1. Restore a green full-example baseline (completed 2026-07-19)

The certificate work exposed a real proof gap first in
`input_cursor_shared_pipeline`: after `input_cursor_init` and
`input_cursor_clone`, the old grouped `execute_rest()` proof depended on two
modular calls accidentally sharing one opaque call identity. Restoring distinct
identities then exposed the same masked dependency in the owned segmented
buffer, owned split buffer, owned string, and owned vector pipelines.

Historical bisection on 2026-07-19 established the exact boundary:

- `1576b80` (`lower bounded execution branches`) passes input-cursor.
- `9ea6739` (`remove replay bookkeeping tactics`) is the first failing commit.
- Before `9ea6739`, every statement reset the opaque-call counter, so both
  modular calls reused `call-havoc:0`. That accidentally made successive
  memory snapshots look identical for unchanged left-cursor loads.
- `9ea6739` correctly gives successive calls distinct havoc identities
  (`call-havoc:0`, then `call-havoc:1`). The existing proof then needs an
  explicit certified transport of the left-cursor bound across the clone call.
- A diagnostic change at `9ea6739` that forces every statement transition to
  reuse opaque call zero makes input-cursor pass again. Do not use that as the
  fix: distinct call identities are required for sound modular execution.

The fix keeps distinct `call-havoc:N` identities and makes the proof boundaries
explicit:

- establish the left cursor's bound, zero position, and data pointer before
  clone so `execute_step()` records checked frame transports;
- re-establish the exact current-snapshot facts needed after clone and take;
- use small pure transitivity/arithmetic theorems instead of relying on hidden
  recursive equality search;
- split peek and return so the returned element identity is certified before
  grouped finalization.

Two bounded kernel gaps were also fixed:

- equality facts can match when both pointer-offset endpoints differ only by
  structurally equivalent memory snapshots;
- memory-load equality tries the existing depth-bounded snapshot/pointer
  resolver before global memory resolution and can combine an exactly equal
  pointer base with an exactly zero index;
- pointer-offset propositions can combine an exactly equal base with an exactly
  zero element offset;
- memory-load transport may use a one-hop pointer-offset fact whose endpoints
  differ only by framed snapshots. This lookup is deliberately restricted to
  memory-load fact transport so ordinary alias and separation checks retain
  their fast exact path.

The global memory-load equality fallback now has a recursion-depth guard. A
limit of two retains the existing symbolic-index framing cases while preventing
the stack overflow seen when unsuccessful equality searches recursively
re-entered memory resolution. This is a termination guard, not a proof rule: at
the limit the resolver returns `false` and the proof must supply an explicit
fact.

The old `initialize`/`disturb` characterization test was removed because it did
not reproduce the real boundary. The small regressions are now
`equality_fact_matching_transports_both_pointer_offset_endpoints`,
`memory_load_equality_combines_equal_pointer_base_and_zero_index`, and
`pointer_offset_equality_combines_equal_base_and_zero_index` in
`src/kernel/tests.rs`.

Focused command:

```sh
CLICK_EXAMPLE=input-cursor cargo test --test examples --quiet
```

The focused projects now verify with distinct call identities. Representative
confirming times on 2026-07-19 were 689 seconds for input-cursor, 29 seconds for
owned-segmented-buffer, 64 seconds for owned-split-buffer, 179 seconds for
owned-string, and 1,286 seconds for owned-vector. The library suite has 313
passing tests, `cargo check --all-targets` passes, and `mdtests` passes. The
complete example corpus passes; the confirming run took 2,330.65 seconds.

Correctness is restored, but grouped-proof and modular-call performance remains
explicit follow-up work; do not use these slow examples as ordinary inner-loop
regressions. A stack sample of the owned-vector run showed most time in modular
call setup while pruning symbolic memory cells and proving separation, not in a
deadlock or an unbounded call-identity loop.

### 2. Make source rewriting total and canonical

This is the clearest remaining `click-expand` bug.

Click accepts a clause such as:

```click
ensures result == x;
```

as an implicit default/`auto` proof. Verification can record a valid expansion,
but `expand_c0_claim_source` currently rejects it because the scanner only
knows how to replace an existing `by` span. The error is:

```text
selected Ensure(...) uses a default proof and has no source proof clause to replace
```

Canonical source policy:

- `format_tactic_certificate()` emits `by { ... }` without a trailing
  semicolon.
- Replacing `by auto;`, `by simp;`, `by frame;`, or `by { ... };` consumes the
  optional proof-clause semicolon, as the current implementation does.
- Expanding an omitted proof replaces its terminating semicolon with the
  canonical `by { ... }`; it does not insert before and preserve that
  semicolon. This makes the first expansion identical to later expansions.
- Whitespace outside the edit is preserved. The replacement's internal layout
  is canonical and indented relative to the edited clause.

Implementation direction:

1. Make the source locator return an explicit source edit rather than assuming
   every edit was an existing `by` clause. For example:

   ```rust
   enum ProofSourceEdit {
       ReplaceExplicitProof(Range<usize>),
       ReplaceDefaultTerminator(Range<usize>),
   }
   ```

   A single `Range<usize>` remains mechanically sufficient if the two cases
   are still distinguished in diagnostics and tests.
2. In `find_claim_proof_span`, encountering the selected clause's top-level
   semicolon before a `by` should return the semicolon's byte range as the edit.
3. Apply the canonical policy above for explicit and omitted proofs.
4. Keep the source scanner aligned with the actual Click lexer. Claim-span
   scanning happens after verification, but the same scanner is also used by
   `verifying_source_paths` before full parsing, so malformed input must return
   `ClickError` rather than panic. Preserve byte offsets while iterating at UTF-8
   character boundaries, and recognize every whitespace character the parser
   accepts. Continue treating escaped string and character literals atomically
   so proof-looking text inside them cannot affect delimiter or `by` detection.
   Click comments are not currently valid syntax; do not add comment support
   solely for this task.
5. A grouped proof cannot be omitted: without a function-level `by`, the parser
   represents the function as independent claim proofs, each possibly default.
   Keep a precise error for selector `grouped` when no grouped proof exists and
   add a test for it.
6. After applying the edit, call `verify_c0_sources` on the rewritten sidecar
   before returning it. A bad span, malformed layout, or unreplayable printed
   certificate must therefore fail without emitting source.
7. Verify semantic selection as well as string shape: the selected proof is
   explicit and contains no smart tactic after reparsing, while neighboring
   claims remain byte-for-byte unchanged.

Tests to add or update in `src/lang/click/tests.rs`:

- Replace `source_expander_rejects_default_proofs_without_rewrite_spans` with a
  successful omitted-ensure round trip.
- Add omitted/default effect coverage if effects permit an omitted proof.
- Add a default-proof idempotence test.
- Include Unicode whitespace, escaped literals, and proof-looking text in an
  unrelated string literal to protect source-span behavior.
- Confirm malformed or unterminated literals return `ClickError` without a
  panic from `verifying_source_paths`.
- Confirm that expanding one omitted claim leaves neighboring claims unchanged.
- Confirm that `grouped` gives a precise error for a function with only
  individual/default proofs.
- Confirm that a source edit which does not re-verify is never returned.

Acceptance criteria:

- Every syntactically valid implicit smart proof can be expanded.
- `expand_c0_claim_source` itself re-verifies the expanded sidecar before
  returning it.
- Expanding the same claim again produces byte-identical source.
- Source outside the selected proof edit is byte-identical.

### 3. Add a corpus-wide selectable-claim audit

The current tests cover selected `simp`, branched `simp`, contextual `frame`,
grouped proof, selected-claim replacement, and idempotence cases. They do not
establish that every selectable claim proof in the examples can be expanded.

Build an automated audit over all example projects:

1. Load C and Click files using the same project rules as `tests/examples.rs`.
2. Verify each original sidecar once.
3. Enumerate each independently selectable proof:
   - every non-grouped ensure by index;
   - every non-grouped effect by index;
   - one grouped proof per function, not once per theorem generated from it.
4. For every selectable proof, regardless of whether its surface spelling is
   default, one smart tactic, or an explicit script, require
   `expanded_proof_certificate()` to succeed. This is stronger and simpler than
   trying to classify nested scripts before auditing them. Report the function,
   claim, source proof form, `ProofKind`, and `expansion_blocker()` on failure.
5. Print the certificate as Click using the production formatter.
6. Starting from a fresh copy of the original sidecar for each selected claim,
   call `expand_c0_claim_source` and verify the rewritten sidecar.
7. Re-expand that same claim and require byte-for-byte idempotence.
8. Reparse the rewritten source and ensure the expanded claim contains no smart
   tactic at any nested depth. Certificate validation is the primary check;
   inspecting reparsed source also catches editing the wrong span.

Use a fresh original sidecar per claim. Sequentially expanding multiple claims
in one mutable string makes failures harder to attribute and is unnecessary for
the accepted one-claim scope.

The audit must also inventory, but not attempt to expand, proof-bearing syntax
outside `CProofClaim`: pure theorem ensures, loop `initialize`/`preserve`
proofs, and structural-item proofs. Keep that inventory visible in the test or
maintainer output so adding a new proof site cannot silently broaden claims of
coverage. A later selector/API design can turn those entries into audited
source expansions.

Prefer sharing the example-project loader instead of copying the filesystem
logic from `tests/examples.rs`. Keep `CLICK_EXAMPLE=<directory-name>` support so
individual projects can be debugged without running the whole corpus.

If the audit finds a proof that verifies but cannot expand, treat that as a
correctness inconsistency in the smart/simple design. Classify the blocker as
one of:

- an internal replay operation lacks a surface simple tactic;
- a kernel proposition lacks a checked Click spelling;
- a spelling cannot be reconstructed at the required snapshot/program point;
- the explicit certificate needs a premise that smart verification obtained
  from hidden ambient context;
- control-flow lowering does not preserve the successful replay structure;
- source selection or rewriting is wrong even though the certificate is valid.

For each blocker, first add a minimal test, then fix the missing deterministic
rule or mapping. Do not make the printer guess source or let certificate replay
call the original smart tactic.

Acceptance criteria:

- Every selectable proof in every green example project has a certificate.
- Every selected expansion re-verifies from normal inputs.
- Every selected expansion is idempotent.
- Failures identify the exact project, sidecar, function, and claim.
- Out-of-scope proof-bearing sites are explicitly inventoried and are not
  described as covered by this audit.
- The audit runs in the normal test suite, unless measured runtime makes a
  separately documented CI test necessary.

### 4. Fix audit blockers one at a time

Do not predict or preemptively generalize beyond blockers found by the corpus
audit. For each failure:

1. Record the smart tactic's exact successful result and first expansion
   blocker.
2. Reduce it to a focused unit test or mdtest.
3. Identify the finite sequence of simple proof steps that should justify it.
4. Confirm every step can be written in Click source.
5. Add the narrow missing surface tactic or lowering rule if necessary.
6. Make the smart planner emit that sequence.
7. Replay the certificate from ordinary proof inputs.
8. Round-trip the printed source through parsing and verification.
9. Re-run the focused example, then the complete audit.

An acceptable fix may make the expanded proof larger. It may not hide search in
a newly named "simple" tactic.

Keep each blocker fix in its own commit after the audit-harness commit. Do not
mix several new kernel rules into one speculative generalization.

### 5. Update the proof-tactic documentation

`docs/proof-tactics.md` currently contradicts itself. It says Click does not
expose an expansion mechanism, then later documents `click-expand`.

Update it after omitted-clause support and the audit blockers are settled:

1. Remove the stale statement that no surface expansion command exists.
2. Explain that `click-expand` expands one selected C claim proof and prints the
   full rewritten sidecar to stdout.
3. Document zero-based selectors and relative `verifying` path resolution.
4. Add one small before/after example, including an omitted/default proof.
5. State the reducibility invariant: successful smart tactics inside a selected
   proof must yield surface-expressible simple/control-flow certificates.
6. Explain that `expansion_blocker()` is a defect-oriented diagnostic and that
   partial or non-verifying source is never emitted.
7. Document the exact scope boundary: ensures, effects, and grouped C function
   proofs are selectable; theorem, loop-phase, and structural-item proof source
   is not yet selectable.
8. Keep the distinction between a tactic, a proof step, a smart tactic, and a
   control-flow tactic consistent throughout code comments and docs.
9. Document the corpus audit and its focused `CLICK_EXAMPLE` workflow for
   maintainers.

Also search all docs and comments for stale claims about expansion availability:

```sh
rg -n "expand|expansion|certificate|proof command|proof step" docs src tests
```

## Near-Term Execution Plan

Treat the work above as five mergeable milestones:

1. **Green baseline:** reduce and fix the `input-cursor` modular-call fact
   derivation, then run every example. Stop and repair any additional baseline
   failure before changing expansion behavior.
2. **Transactional source rewrite:** support omitted ensure/effect proofs under
   the canonical semicolon policy, re-verify output in the production API, and
   land the focused span/idempotence tests.
3. **Audit harness:** share the example loader, enumerate every selectable
   proof from a fresh sidecar, and land the audit even if it initially reports a
   small explicit list of known expansion blockers. Do not weaken assertions to
   make blockers disappear.
4. **Blocker burn-down:** remove that list one blocker and one regression test
   at a time. Re-run the focused project after each fix and the complete audit
   before each blocker commit is complete.
5. **Closeout:** remove stale documentation claims, run the full verification
   matrix, and record the out-of-scope proof-site inventory as the next
   expansion project.

The first useful checkpoint is milestones 1 and 2: a green verifier baseline
and a source rewriter that handles every currently valid selector spelling
without returning malformed output. The audit should follow immediately; avoid
adding more CLI features between those checkpoints.

## Design Constraints

Preserve these constraints while completing the roadmap:

- **Surface completeness:** every certificate leaf has Click syntax and normal
  tactic semantics.
- **Bounded simple tactics:** simple tactics perform one deterministic,
  bounded operation and do not search for tactic sequences.
- **Explicit premises:** contextual facts used by execution or theory rules
  appear in `using` clauses or explicit prior tactics.
- **Point-aware facts:** memory-dependent propositions are reconstructed and
  checked at their exact snapshots/program points.
- **Certified transport:** a fact moves between memory snapshots only through a
  checked frame/effect transport rule.
- **No hidden replay:** expanded proofs start from normal proof inputs and do
  not reuse planner-only state.
- **No partial output:** one unsupported node rejects the whole expansion with
  a useful blocker.
- **Verified output:** the source API re-verifies its completed edit before
  returning it; source-location bugs must not escape as CLI output.
- **Canonical output:** formatting is parseable and stable enough for
  byte-identical re-expansion.
- **Control flow stays explicit:** `have`, proof `if`, and `advance` may organize
  certificates, but all nested leaves must satisfy the same surface rule.
- **No recursive catch-all solvers:** do not revive recursive proposition
  rewriting, unbounded predicate unfolding, or multiple consumer-specific
  equality engines to make an example pass.

## Important Files

- `src/bin/click-expand.rs`: CLI argument parsing, sidecar loading, stdout.
- `src/lang/click/expansion.rs`: source discovery, claim selection, source-span
  location, canonical explicit-proof/default-terminator replacement, and final
  rewritten-source verification.
- `src/lang/click.rs`: `VerifiedCTheorem`, `TacticCertificate`, validation, and
  formatting API.
- `src/lang/click/proof.rs`: smart planning, replay, surface trace recording,
  proposition spelling, and expansion blockers.
- `src/lang/click/tests.rs`: focused verification and source-expansion tests.
- `tests/examples.rs`: complete example-project verification and
  `CLICK_EXAMPLE` filtering.
- `docs/proof-tactics.md`: simple/smart taxonomy and certificate design.
- `examples/input-cursor/`: sound distinct-call snapshot/transport regression;
  currently also the main example-suite performance outlier.

## Verification Commands

Run focused checks while iterating:

```sh
cargo test --lib source_expander --quiet
cargo test --lib smart_simp_expansion --quiet
CLICK_EXAMPLE=input-cursor cargo test --test examples --quiet
```

Run the full checks before each roadmap commit is considered complete:

```sh
cargo fmt --check
cargo check --all-targets
cargo test --lib --quiet
cargo test --test mdtests --quiet
cargo test --test examples --quiet
git diff --check
```

The mdtest suite currently takes roughly 45 seconds. A focused input-cursor
success took 689 seconds after the soundness fix. Keep the two fast kernel
regressions in the inner loop and treat the grouped-proof runtime as separate
performance work. Slowness that grows dramatically from a small proof remains
a likely sign that hidden recursive search or poor proof-context scaling has
been introduced.

Manual CLI smoke test:

```sh
cargo run --quiet --bin click-expand -- \
  path/to/example.click function_name ensure:0
```

Redirect its stdout to a temporary `.click` file and verify that file using the
same C sources when manually checking source layout.

## Current Test State

Last known results after the soundness fix:

- the two focused kernel snapshot/pointer regressions pass;
- `CLICK_EXAMPLE=input-cursor cargo test --test examples
  example_projects -- --nocapture`: passed in 689 seconds;
- the complete unit, mdtest, and example suites still need their final
  post-change run before committing.

Do not claim corpus-wide expansion support until the full examples are green
and the expansion audit itself passes.

## Definition of Done

`click-expand` is complete for the current selectable C-claim boundary when all
of the following are true:

- Omitted/default proofs can be expanded.
- Every selectable example proof can produce a validated surface certificate;
  every smart tactic nested within it is lowered.
- Every selected example proof can be source-expanded and reverified.
- Re-expansion is byte-identical.
- The production source API re-verifies the edited sidecar before returning it.
- Expansion failures identify a precise unsupported item and emit no partial or
  non-verifying source.
- The full unit, mdtest, and example suites pass.
- Documentation accurately describes the command and the smart-to-simple
  invariant.
- No certificate depends on internal-only tactics, hidden ambient facts,
  unbounded search, or replay-only state.
- Proof-bearing constructs outside `CProofClaim` are inventoried explicitly and
  are not represented as covered by the selectable-claim audit.
