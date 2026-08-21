# Triaging Proof Failures

A failed proof is evidence, but it does not by itself identify a Click bug.
Classify the failure before changing the proof engine, the specification, or
the C source. This keeps ordinary proof development separate from language
gaps and tooling defects.

Click is intended to verify existing C. For C within Click's supported
semantics, do not rewrite otherwise-correct implementation code merely to make
a proof easier. Keep the original source pattern in the regression and put the
adaptation or fix in the contract, proof, language, verifier, or kernel.

## Triage order

### 1. Check the claim and its assumptions

First ask whether the property is true on every execution admitted by the
contract and Click's C semantics. Look for a false postcondition, a missing
precondition, undefined behavior, an invalid loop invariant, or an effect that
the contract failed to describe.

If the claim is false or its required assumption was never declared, repair
the specification or proof. That is ordinary proof development, not a Click
issue. Do not add a precondition merely because it makes automation succeed;
the precondition must describe a real requirement of the C operation.

### 2. Check the supported-semantics boundary

Determine whether the C construct and the desired property are within Click's
documented semantics. A deliberately unsupported construct is a current
limitation. If supporting it is part of Click's intended scope, record it as
**missing functionality** rather than treating the program as erroneous.

A semantics-preserving translation into Click's documented C0 subset may be
useful while support is incomplete, but it must be identified as such. It is
not evidence that Click verifies the unchanged source form.

### 3. Replace broad search with explicit proof steps

Smart tactics are bounded, incomplete heuristics. A prompt and actionable
failure from `auto`, `execute()`, `simp()`, `frame()`, or another smart tactic
does not establish an engine bug. Split the task into smaller searches or use
simple tactics with explicit premises.

The result distinguishes three important cases:

- If an explicit proof works and replays, the smart tactic's miss is at most an
  **ergonomic or automation problem**. Improve it only when there is a useful
  general pattern; do not retune shared heuristics just to make one broad
  search pass.
- If the needed valid reasoning cannot be expressed through Click's proof
  language or contracts, the failure is **missing functionality**.
- If an existing, documented proof operation applies but Click rejects it or
  gives it the wrong meaning, the failure is a **correctness bug**.

These labels describe the boundary that needs work. An ergonomic problem can
later justify a language feature, and investigation of an apparent missing
operation can reveal a correctness bug in an existing one.

### 4. Separate tooling reliability from proof search

Some behavior is a tooling defect regardless of whether the underlying claim
is easy to prove. Treat the failure as a high-priority **tooling reliability
bug** when:

- a tactic exceeds its enforced class budget instead of failing promptly;
- smart search reports success but its certificate does not replay;
- `click verify`, `click profile`, `click expand`, and `click audit` disagree;
- expansion emits an unverifiable rewrite or operates on a failing proof;
- a normal error produces an enormous or misleading internal-state dump; or
- an interrupted command leaves verifier processes running.

Stop affected feature or example work and reduce this problem first. Do not
hide it by raising limits, adding arbitrary search caps, weakening the example,
or inserting irrelevant proof bookkeeping. See
[Performance Tools](performance-tools.md) and
[Testing Click](../internals/testing.md) for the operational workflow.

## Classifying smart versus simple tactics

Classify tactics by whether they select a proof rule, not by whether the user
listed their input facts. A tactic that receives hints and chooses among
normalization, rewriting, arithmetic, transport, framing, or other theories is
smart and must expand. A simple tactic checks one named rule from explicit
evidence with work proportional to that certificate. Simple replay must not
fall through alternate strategies or reconstruct a proof from ambient history;
if expansion cannot express the selected rule, that is a certificate-language
issue.

## Classification summary

Use the narrowest description supported by the evidence:

- **Ordinary proof development:** the claim is false, the contract is
  insufficient, or the proof has not yet supplied available reasoning.
- **Documented limitation:** the source or property is intentionally outside
  the currently supported scope.
- **Ergonomic or automation problem:** an explicit supported proof works, but
  a smart tactic misses a general case it would be useful to handle.
- **Missing functionality:** the true in-scope proof needs a fact, contract
  form, semantic rule, or simple proof step that Click cannot express.
- **Correctness bug:** an existing supported rule, semantic model, or proof
  operation rejects a valid use or accepts an invalid one.
- **Tooling reliability bug:** budgets, diagnostics, certificate replay, or
  the profile/expand/audit workflow violates its guarantees.

When evidence is incomplete, say what is known instead of guessing a label.
For example: "smart `frame()` failed; explicit resource transport has not yet
been attempted." The next experiment should be the smallest one that
distinguishes the remaining categories.

## What to put in an issue

An issue should preserve enough information to test the classification:

- a minimal regression containing the original C pattern;
- the contract and property being proved, including why the claim is true;
- the smallest explicit proof attempted and the exact point where it stops;
- the expected category and the evidence for it;
- whether verification, certificate replay, expansion, and audit agree;
- timing and diagnostic behavior when tooling reliability is involved; and
- concrete acceptance criteria.

Do not leave the only reproduction inside a large example or an uncommitted
worktree. If reduction changes the source pattern that caused the failure, it
is not yet an adequate regression.
