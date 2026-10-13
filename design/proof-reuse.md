# Proof reuse and case structure

Design for [design-review](../issues/design-review.md) item P5 ("copy-paste
across case files and sidecars"). It measures where the repetition in
`examples/rbtree-erase` comes from, compares that with what Dafny, Verus,
Lean and separation-logic tools do, and lists what Click needs. It assumes
[smt-auto.md](../issues/smt-auto.md) lands. Measurements are from master at
`101ad5c7`.

## Summary

Most of the repetition is not a missing language feature:

- **Superseded increments.** Three quarters of rbtree-erase is development
  increments that a general proof has already superseded.
- **Mirror arms.** About half of the general color-repair proof is the
  left/right mirror of the other half.

Dafny and Verus have no symmetry feature. Their mirror arms are short because
each step is automatic, so the duplication costs little. Lean and Coq also
have automation, and in addition one tactic script can close several goals.

Click lacks four things:

1. automatic unfolding of recursive specification functions;
2. automatic folding and unfolding of resources;
3. one proof script reused across goals;
4. the habit, and the tooling, of keeping one general contract per function.

## Measurements

### Superseded increments

`rbtree-erase` has 41 sidecars and 39,582 lines.
`rbtree_erase_color_flips_red_all.click` (4,236 lines) proves the unchanged
`____rb_erase_color` under its general precondition: a one-black-level
deficit context with consistent parents. It has no case selector; a coverage
theorem derives the case split from the deficit invariant.

Twenty-two older color-repair sidecars each prove one case or a union of a
few cases. Every one of them is subsumed by that general proof. Together they
are **29,160 lines, 74% of the example**. They remain because mutation tests
point at them: 82 references in `tests/`, against 2 for the general proof.

The critique's "`__rb_change_child` contract copied into 24 files" is also in
these increments. Each one re-proves the helper inline because it predates
`rbtree_change_child.click`. The current proofs import that file, so contract
import works and is not a gap.

### Per-case contracts for `rb_erase`

`rb_erase` is verified in 11 sidecars, each under a case-selecting contract.
For example, `rbtree_erase_black_successor_wrapper.click` requires a black
root whose right child is a black leaf. No general `rb_erase` contract exists
yet; the rbtree issue lists wrapper integration as remaining work.

The language can already express one. A proof `match` whose arms each run to
function exit is supported (`docs/concepts/proof-scripts.md`). Conditional
resources can give a contract ownership that depends on the outcome: for
`__rb_erase_augmented`, either a balanced root and a null fixup parent, or a
deficit context and the parent to repair. This has not been tried yet.

### Mirror arms in the general proof

The loop's `preserve` proof matches on the context. The `Context::Right` arm
is 1,377 lines and the `Context::Left` arm is 1,385. After swapping
`Left`/`Right` and `left`/`right`, all but about 370 lines of each arm are
identical. Most of the remaining differences come from two sources:

- **Constructor argument order.** The child arguments of
  `RbTree::Node(id, parent, color, left, right)` must also be swapped, which
  a textual swap misses.
- **Comments.**

A few `step()`s really differ, because the Linux C is not symmetric: the two
arms read the sibling at different points. The theorem
section is also written in left/right pairs.

### What one arm is made of

The 1,377 lines of the `Context::Right` arm:

| Kind | Lines | Example |
|---|---|---|
| `have` | 617 | |
| … of which one rewrite then `assumption`/`normalize` | 222 | `have sm == Node(...) by { rewrite(sm == ...); normalize(); }` |
| unfolds of recursive spec functions | about 70 | `color_bit`, `rb_reparent`, `plug`, `rb_tree_parent_consistent` |
| resource `fold`/`unfold` | about 100 | `fold(rb_at(...))` 36, `ctx_at` 11, `rb_child_links` 22 |
| `step` | 106 | |
| `let` | 79 | |
| `fact`, `mark` | 74 | |
| `apply` | 61 | |

Many `have` lines restate a whole model term after a pointer update, and
some of those run to over 1,000 characters.

## What other systems have

| Technique | Dafny | Verus | Viper / VeriFast | Lean / Coq / Isabelle | Click |
|---|---|---|---|---|---|
| One verification condition covers every path; no per-step script | yes | yes | yes | no | no; each arm is scripted |
| Congruence and linear arithmetic per step | SMT | SMT | SMT | `simp`, `omega` | hand-written; [smt-auto.md](../issues/smt-auto.md) |
| Recursive spec functions unfold automatically | fuel, default 1–2 levels | fuel | heuristics | `simp [f]` equation lemmas | explicit `unfold` |
| Heap facts carry across steps (framing) | `modifies`/`reads` | ownership types | permissions | n/a | partly; facts restated |
| Data-structure predicates open and close themselves | n/a, no separation logic | ownership types | Viper explicit; VeriFast auto-open/close | n/a | explicit `fold`/`unfold` |
| One script closes several goals | no | no | no | `<;>`, `all_goals`, Ltac, Lean macros | no; user tactics run no C |
| Symmetry (`wlog`, mirroring) | no | no | no | `wlog`, sometimes | no |
| Several contracts for one function, combined | no | no | VST: specification intersection | any number of theorems | one contract per sidecar |
| Contract import | modules | modules | yes | yes | yes |

## Needs

These are in order of value per unit of work. Each one stands on its own.

### R1. Retire superseded increments (process)

When a general proof subsumes an increment, delete the increment and point
its mutation checks at the general proof. The same applies to the `rb_erase`
case wrappers once a general contract lands. For rbtree-erase this removes
about 29,000 of 39,600 lines with no verifier change.

Cost: mutation checks against the 4,236-line proof are slower than against a
200-line case file. Measure them, and move them to nightly if they exceed the
gate budget.

Add a rule to `docs/internals/testing.md` or the examples guide: an example
keeps only its general proof and that proof's regressions.

Done: the 22 increments are deleted. Their 80 nightly mutation tests named 39
distinct C mutations; two were already checked against the general proof and
the other 37 now are. `examples/rbtree-erase` went from 44 sidecars and 39,582
lines to 22 sidecars and 10,422 lines. The gate is unaffected: the example and
all of these mutation tests were already nightly. The rule is in
`examples/README.md`.

### R2. One general contract per function

The norm is one contract per function. Cases become `match` arms inside one
proof, so the shared C prefix is executed once.

Prototype a general `__rb_erase_augmented` contract with an outcome-dependent
conditional resource, and a general `rb_erase` on top of it. If that works,
no feature is needed.

Not proposed: VST-style contract intersection, in which separate case
contracts are combined by a checked coverage obligation. It would keep
per-case development but re-execute the shared prefix once per case.
Reconsider it only if R2's prototype shows the single-proof form failing on
size or speed.

### R3. Automatic unfolding of recursive specification functions

`simp` unfolds a recursive pure function when its argument is a known
constructor, to a fixed fuel, as Dafny does. The unfolded equation is a
checked rewrite in the expansion. This removes most of the 70 explicit unfolds
per arm, and most model-term restating, because the solver can see through
`plug` and `rb_reparent`.

[smt-auto.md](../issues/smt-auto.md) keeps recursive predicates out of scope.
This item is different: it covers pure functions over constructors, which are
bounded and decidable at fixed fuel. It can be added as a stage of that issue
or done separately.

### R4. Automatic opening and closing of resources

When a step reads or writes a field covered by a folded recursive resource
whose model is known to be one constructor, `step()` unfolds that layer. At
function exit, loop back edges and arm joins, Click refolds layers whose
fields still match the definition. This follows VeriFast's auto-open/close
and Viper's fold heuristics. It must stay bounded: one layer per access, and
no search over which resource to open. Explicit `fold`/`unfold` remain for
everything else. This targets about 100 lines per arm.

### R5. One script for several goals

Allow one proof block to close several arms whose scripts are the same up to
a renaming. For example:

```click
match c.model {
    Context::Right(id, above, pc, sm, um) | Context::Left(id, above, pc, sm, um) => { ... },
}
```

Each listed arm runs the shared block separately, against its own C path, so
the kernel checks each instance independently. A direction-generic model
layer makes the text identical: `child(d, t)` and `Context::Child(d, ...)`
in place of separate left and right constructors, with lemmas proved once
over `d`.

This is the Lean `<;>` idea restricted to arms, and it involves no
metaprogramming. It does not help where the C differs between arms; such
lines stay per arm.

Measure it after R3 and R4. If they shrink each arm to tens of lines, as in
Dafny, R5 may not be worth its language surface.

Not proposed: checked mirroring of C code. The Linux arms are not textual
mirrors, and checking that two C regions are mirror images is a large new
trusted component.

## Expected effect on rbtree-erase

These are estimates, to be replaced by measurements.

- R1 removes about 29,000 lines.
- In the general proof, [smt-auto.md](../issues/smt-auto.md) stage 1, R3 and
  R4 target about 400 of 1,377 lines per arm: the 222 one-line equalities,
  the recursive unfolds and the resource bookkeeping. Facts that no longer
  need restating should account for a large share of the remaining `have`s.
- R5 would then halve what remains of the mirrored arms and theorems.

## Validation

- R1: delete the superseded files and port their mutation checks. Record the
  example's line count and gate time before and after.
- R2: prove general `__rb_erase_augmented` and `rb_erase` contracts. Record
  their size against the 11 wrappers they replace.
- R3 and R4: mdtests for one fuel unfold, one automatic open on a field read,
  and a refold at a join. Add negative cases for an unknown constructor (no
  unfold) and a field mismatch at refold (refused). Then rewrite one arm of
  `rbtree_erase_color_flips_red_all.click` and record its size and time.
- R5: only after R3 and R4 are measured.
