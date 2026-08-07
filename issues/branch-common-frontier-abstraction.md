# Give `branch` a principled common-frontier abstraction

## Problem

Frontier-local `branch` proves both C arms and requires every nonreturning arm
to reach the `if` statement's common continuation. It nevertheless retains a
separate symbolic replay context for each arm. That is useful for precise
path-sensitive execution, but it is not yet a complete replacement for
`reach`: `reach ... ensuring` also constructs one explicit abstract state and
forgets branch-only facts and ghost resources.

The distinction appears in `proof_reach_composite_resource_transform.md`.
Both arms call different helpers and fold the same `ready_bundle(key)` before
the common return. Replacing the scoped `reach` and logical `if` with a
frontier-local `branch` reaches the correct source frontier, but ordinary
verification rejects the first retained arm because its path-specific
`left_path`/`right_path` resource representation does not match the complete
function certificate.

This is not a request to make `frame` smarter and not a reason to rewrite the
C. The proof language currently lacks a frontier-local replacement for the
state-abstraction role of `reach`.

## Intended regression

Preserve the existing C and resource definitions from
`mdtests/proof_reach_composite_resource_transform.md`. The intended forward
proof is structurally:

```click
step();
branch {
    then {
        step();
        fold(ready_bundle(key));
    }
    else {
        step();
        fold(ready_bundle(key));
    }
}
observe(ready_bundle(key));
step();
simp();
```

The common frontier should retain `selected == key` and ownership of
`ready_bundle(key)`, while branch-only path tokens may be forgotten according
to Click's resource rules.

## Design question

Decide where common-frontier abstraction belongs before changing syntax:

- Prefer a deterministic join performed by `branch` when the two arms reach
  the same frontier, retaining facts and resources that have a common checked
  representation and abstracting changed locals through the kernel's existing
  join model.
- If important common facts cannot be inferred deterministically, add a
  frontier-local explicit interface to `branch` rather than restoring detached
  source locations. Any spelling should describe the state immediately after
  this branch, not introduce a second execution cursor.
- Keep ordinary `have`, `observe`, `fold`, and other forward tactics usable
  immediately after the join. Do not require an assertion list when the common
  state is already exact.

The join must not be a heuristic smart search whose occasional failure changes
proof correctness. It should either compute a checked abstraction
deterministically or require explicit, kernel-checked interface facts.

## Acceptance criteria

- The composite resource-transform regression verifies with frontier-local
  `branch` and no `reach`.
- Common scalar, memory, composite-resource, and old-state facts survive when
  both arms establish them.
- Arm-only facts and resources cannot leak into the common context.
- Differently spelled but propositionally equal common resources are joined by
  checked equality, not pointer-name coincidence.
- A one-arm return and nested branches have defined behavior.
- The resulting proof and every smart tactic in it pass `click audit`.
- Existing C and resource declarations remain unchanged.

## Blocks

This blocks migrating the resource-transform use of `reach`. It also owns the
design decision behind the reach-specific hiding tests
`proof_reach_hides_branch_facts.md` and
`proof_reach_hides_unexported_requirement.md`: their behavior needs a
frontier-local home before `reach` can be removed. Direct branch continuations
which need no abstraction can migrate independently.
