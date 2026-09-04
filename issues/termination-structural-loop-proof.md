# Support resource transitions for structural recursion inside ranked loops

The read-only slice of structural recursion inside a ranked loop landed on
2026-09-03. `mdtests/c_decreases_resource_recursive_in_loop.md` proves an
unchanged C loop that observes a recursive list resource and calls itself on
the direct child; the paired parent-call regression remains rejected. The
termination checker also now ignores known pointer-valued branch guards while
checking the scalar loop ranking, so a guard such as `node->next != 0` does not
turn a valid structural path into an arithmetic-measure error.

## Remaining gap

A structurally decreasing recursive call that consumes or mutates the
resource inside a ranked loop still needs a sound loop-back-edge rule. The
resource and heap-lifetime state must be preserved on continuing iterations;
the loop proof must not recover a consumed child or hide a mutation behind
the loop invariant. The existing single-call destructor regression does not
cover this repeated-region boundary.

## Intended regression

Add an mdtest with unchanged C whose function has a separately ranked finite
loop, a directly recursive resource measure, and a recursive call on a direct
child that consumes or mutates the child resource. The proof should exercise
the real resource transition and then either preserve the parent/sibling
authority for a continuing iteration or report the precise unsupported
transition. Include a negative case showing that a consumed or freed resource
cannot be resurrected by the loop join.

## Acceptance criteria

- A continuing loop path preserves exactly the resource populations and heap
  lifetime required by the next iteration after a valid child transition.
- No resource ownership, allocation authority, or mutation is duplicated or
  recovered from a caller assertion at the back edge.
- Direct-child structural descent remains independently checked, and parent
  or unrelated calls remain rejected.
- The proof stays on the checked execution and certificate path; no hidden
  body rerun or C rewrite is introduced.
- `scripts/check.sh` passes.

Related: [termination-ranking-coverage.md](termination-ranking-coverage.md);
[arena-resource-ownership.md](arena-resource-ownership.md).
