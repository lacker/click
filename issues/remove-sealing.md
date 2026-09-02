# Make the proof object validate its own execution chain

## Status

Filed 2026-09-02 after the double-execution work landed. Nothing here is
started. Slices are listed in landing order; each lands green on its own
with the current end-of-proof check still in place as a backstop, and the
last slice deletes that check.

## Violated invariant

The proof object is the kernel's authority for a proof-directed execution.
Every operation on it either advances a kernel-tracked frontier or is
rejected at that operation. When the proof object reports that a function
proof is complete, the checked whole-function execution that claim and
contract certification consume must follow from it directly, with no
second validation pass and no way for that pass to fail.

Today that is only half true. Proof-case arms, resource observations and
rewrites, branch joins, and the checked function entry are validated when
they are recorded. Statement and condition steps are not:
`ExecutionProofCore::record_statement_transition` and
`record_condition_transition` append a kernel theorem and its fact context
without checking that the theorem names the frontier's next source
statement or starts from the frontier's running state. The surface driver
maintains the running state and frontier itself and is trusted to record
the matching theorem.

The chain is validated instead by `checked_c_function_execution_from_proof_evidence`
in `src/kernel/api.rs` (the "sealer"): at the end of the proof it walks
each retained trace against the C source, checks statement identity and
order (with `Skip` and loop-head handling), state continuity between
consecutive theorems, premise retention against the recorded contexts,
branch arms and joins, case-partition exhaustiveness, the entry state, and
agreement between each trace's outcome and the path the surface published,
then composes the whole-function theorem and applies the contract's exit
rule. Its failures are `instrumentation::SealRefusal`, counted by the
body-rerun ratchet (every pin is zero). That walk is a second
representation of the proof's validity: a proof object can look complete
while its trace is unsealable, and the word "sealed" now names a state the
proof object cannot see. The refusal count being zero says the drivers are
well behaved, not that the checks exist twice.

## Intended regression

Kernel tests on `ExecutionProofCore`: recording a statement theorem for a
statement other than the frontier's next one, from a state other than the
running state, or with a premise the recorded context does not retain, is
rejected by the record call itself, before any later step, and a proof
object reporting completion yields its checked function execution without
a failure path. The existing sealer tests in
`src/kernel/tests/contract_execution_tests.rs` (`sealing_*`) become tests
of the record calls and of completion. The fixture harnesses keep pinning
the contract-fallback census at zero; the seal-refusal table disappears.

## Slices

Each slice is one worktree, one green `scripts/check.sh`, one fast-forward.
The sealer stays in place and must keep refusing nothing through slice 6,
so every slice is checked by the harnesses against the walk it is
replacing.

1. **Per-trace progress.** Give each retained trace a kernel-owned progress
   record: running state, remaining source, completed outcome, current
   assumptions, retained interface facts. Initialize it at the checked
   function entry (or the bound entry state) with the function body as the
   source. Copy or split it wherever traces fork (`record_statement_outcomes`,
   `fork_outcome_evidence`) and derive it at joins. No checks yet; the
   sealer is untouched. This is bookkeeping only and lands first so the
   later slices are small.
2. **Statement steps.** `record_statement_transition` and
   `record_statement_outcomes` check the theorem against the trace's
   progress the way the sealer does (source statement with `Skip` handling,
   state continuity modulo definitionally equal resource representation,
   premise retention against the recorded context and candidate facts) and
   advance the progress from the theorem's outcome. A failing record call
   returns an error the driver reports at that step. Move the helpers the
   sealer uses (`split_proof_evidence_statement`,
   `proof_evidence_premises_are_retained`, the state match) into the proof
   module; the sealer calls the moved code.
3. **Condition steps.** The same for `record_condition_transition`: `if`
   and `while` selection, loop-head re-entry, pending heap allocation
   resolution.
4. **Resource observations, rewrites, and case arms.** Advance the
   progress state on an observation or rewrite (already kernel-checked) and
   the progress assumptions on a case arm, including an arm recorded after
   a path's returning statement.
5. **Branch joins.** The join record calls check that each arm's progress
   ended at the parent's common tail with the joined state (or the
   interface successor facts) and advance the parent's progress; the
   sealer's recursive branch walk becomes redundant.
6. **Completion.** Add `ExecutionProofCore::checked_function_execution(...)`
   deriving the whole-function execution from the finished traces: path
   count from the traces themselves, the contract's exit rule per trace, the
   published path's outcome checked against the trace's (a check of the
   surface's publication, kept as an ordinary error), case partitions
   exhaustive. Claim finishing calls it. Compare its output with the
   sealer's over both harnesses before the next slice.
7. **Delete the sealer.** Remove `checked_c_function_execution_from_proof_evidence`,
   `seal_proof_evidence_events`, `SealRefusal`, the seal table of the
   ratchet (`SEAL_REFUSAL_BASELINE` in both harnesses,
   `record_seal_refusal`, the seal half of `body_rerun_census_mismatch`),
   and the `sealing_*` test names; rewrite the docs
   (`docs/internals/proof-objects.md`, `docs/internals/testing.md`) and the
   comments that say "sealed" to say what they mean: the checked function
   execution a completed proof object yields.

## Not in scope

- Deriving the surface's published candidate paths from the kernel traces.
  Slice 6 keeps the publication check; making the traces the only source of
  paths is a later change to claim finishing.
- Claim matching at certification (already lands claims by their completed
  propositions) and the contract boundary's artifact authorization.
- The open kernel-API soundness issues the removal of double execution
  unmasked.

## Acceptance criteria

- `SealRefusal` and `checked_c_function_execution_from_proof_evidence` no
  longer exist; a completed proof object yields its checked function
  execution through one infallible method.
- A statement or condition theorem that does not advance the trace it is
  recorded on is rejected by the record call, with kernel tests for the
  wrong statement, the wrong state, and an unretained premise.
- Both fixture harnesses pass with the contract-fallback census at zero and
  no seal table; harness times do not rise.
- No file under `src/` or `docs/` describes the proof object as sealed or
  unsealed; the glossary needs no new term.
