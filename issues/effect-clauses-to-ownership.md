# Replace `mutable`, `immutable`, and `frame` with ownership

Click has two overlapping ways to bound a function's writes. Resources give
authority: `owns` permits stores and reads, `views` permits reads. Effect
clauses give a footprint: `mutable Y` promises that no cell outside `Y`
changed, `immutable` promises that nothing changed, and the `frame` tactic
certifies either claim from the recorded stores. Callers frame memory across
a call from whichever of the two is narrower.

The footprint is what a caller wants when a callee owns a wide range and
writes a small piece of it. Spelled as authority, that is a view of the whole
and ownership of the piece:

```click
views data[0..n];
owns data[index..index + 1];
```

Ownership then carries the write bound itself: the callee's stores are checked
at each store, and the caller's call-havoc footprint is exactly the owned
piece, so the viewed remainder is preserved with no clause and no `frame`.
This was probed on master at 2d612e9a: the callee verifies a store into the
owned cell, rejects a store into the viewed part, and a caller owning the
whole range proves a viewed cell unchanged `by auto`. `immutable` is the case
with no `owns` at all, which an omitted clause already means.

A previous attempt (the `codex/audit-effect-removal` worktree and its
`claude/codex-effect-removal-snapshot` branch) removed the syntax first and
then repaired every proof it broke, and did not finish. This plan removes the
syntax last. Each step below is its own gated, integrable change.

## Violated invariant

A verified contract expresses write authority and write bounds through one
concept, ownership, in the contract signature. Removing an effect clause must
never widen what a caller may assume, and adding ownership must never grant a
store the source did not perform. No proof step exists whose only job is to
restate what the resource transition already checked.

Today `mutable Y` on a function that owns `X` with `Y` narrower than `X` has
no ownership spelling that callers can use without a quantified
postcondition, loops without an effect clause havoc even memory the body
could not have written, and `frame` closes claims that the store check has
already established.

## Plan

1. **Bound the default loop havoc by ownership.** A loop with no effect clause
   is an unconditional havoc, but a body can only store into owned memory, so
   the havoc may be bounded by the owned resources at loop entry with no
   syntax. A loop still frames every viewed cell and every owned cell it did
   not write into, exactly as a callee does. Watch expansion golden tests:
   more facts survive loops.
2. **Loop-level resource clauses.** `loop { owns p[0..n]; }` gives the loop
   the same shape as a callee: the body's preservation proof runs with the
   loop's owned ranges and views of everything else the function owns, a
   store outside them is rejected at the store, and the loop havoc is the
   call-havoc rule over the loop's owned ranges. The default with no clause is
   everything the function owns. Step-level ownership (`step { owns
   p[i..i + 1]; }`) is deferred until a preservation proof is found that the
   recorded per-iteration stores cannot carry; deriving whole-loop footprints
   from body stores stays in `dynamic-range-frame.md`.
3. **Composite pieces.** Probe and, if needed, support owning a piece inside a
   viewed composite (`views list(node); owns node->value;`): the algebra must
   accept the overlap when `contains` proves the piece inside the composite,
   and two owned pieces at symbolic indexes must compose only with the
   distinctness premise, with a diagnostic that names it.
4. **Migrate proofs, old syntax still accepted.** In examples first, then
   fixtures: `mutable Y` with `owns X` narrower than `X` becomes `views X;
   owns Y;`; `immutable` on a function that owns memory becomes `views`;
   whole-loop and step effects become loop-level `owns` or the default;
   `frame()` and `frame() using { ... }` are deleted where nothing remains to
   prove. Negative fixtures keep their C and are rewritten to the new
   spelling with the same expected failure. The redundancy pass already
   landed for the examples (396d3fec) is the first half of this step.
5. **Callback refinement.** Named callback contracts compare permitted writes
   ("must not grow"). Restate that as ownership refinement: an implementation
   may own no more than the interface owns. Keep the refinement negatives.
6. **Remove the syntax.** `mutable`, `immutable`, and `frame` become parse
   errors with a diagnostic pointing at the ownership spelling (the
   `effect_clause_*_removed.md` and `frame_tactic_removed.md` fixtures in the
   snapshot branch are usable). Remove the kernel effect machinery: the
   `Effect` surface type, `CFunctionContractClaimTarget::Effect`, the loop
   effect checks, `prove_effect_clause*`, and the `frame` tactics. Update
   `docs/concepts/contracts.md`, `aliasing-and-frames.md`,
   `memory-model.md`, `proof-workflow.md`, `proof-scripts.md`, the glossary,
   the tactic inventory, and the grammar.

## Intended regressions

- Step 1: a function owning `p[0..n]` and `q[0..1]` runs a loop with no
  clause whose body writes `p[i]`; after the loop `q[0] == old(q[0])` and a
  viewed cell are provable `by auto`. A body store into viewed memory is still
  rejected.
- Step 2: the same function with `loop { owns p[0..n]; }`; a body store into
  `q[0]` is rejected at the store, and `q[0] == old(q[0])` holds after the
  loop without an invariant.
- Step 3: `views list(node); owns node->value;` verifies a store into
  `node->value` and rejects a store into `node->next`.
- Step 4: every migrated fixture keeps its C and its verdict; the borrowed
  slice, vector push, and ring buffer examples verify and expand with no
  quantified preservation postcondition added for the narrow write.
- Step 6: each removed spelling fails with a diagnostic naming the ownership
  form.

## Acceptance criteria

- A narrow write inside a wider owned range is expressed in the signature as
  a view plus an owned piece, and callers frame the viewed remainder with no
  effect clause and no `frame`.
- Loops frame by ownership by default, and a loop-level `owns` narrows the
  loop's authority and its havoc.
- No fixture or example spells `mutable`, `immutable`, or `frame`, and the
  parser rejects them with a pointer to the replacement.
- Expansion never emits `frame`; expansions of migrated proofs verify
  independently.
- No C source changes, no weakened negatives, no raised tactic budgets, and
  deterministic scaling coverage for any new hot-path work (loop havoc
  bounding, composite piece composition).
- The old effect machinery is deleted rather than left as dead code.
