# Certify structural recursion inside ranked loops

Found while extending `termination-ranking-coverage.md` on 2026-09-03. The
kernel termination checker can inspect a recursive resource call in a loop,
but the surface execution proof currently stops while setting up the folded
resource near the loop back-edge with `smart step selection cannot run past the
loop back-edge boundary`. The only reproduction was an uncommitted prototype,
so this issue records the intended source shape and boundary.

## Violated invariant

A C function with a finite loop and a structurally decreasing recursive call
should be verifiable when its proof has the resource authority required by the
call. The proof driver must preserve the folded parent resource and expose its
direct child at the call without unrolling the loop or changing the C source.

## Intended regression

Add an mdtest with unchanged C whose function owns or views a recursively
defined list resource, runs a separately ranked finite loop, and calls itself
on `node->next` inside the loop. The resource definition should establish the
active guard, the `node->next` field authority, and `contains` the child. The
sidecar should prove the loop invariant and recursive call using normal
`observe`/`unfold`/`frame` steps. A paired negative fixture must reject a call
on the parent or an unrelated pointer even when the loop itself terminates.

## Acceptance criteria

- The positive regression reaches the loop body, authorizes its child field,
  and certifies both the loop ranking and direct structural descent.
- Resource authority remains scoped and is neither duplicated across loop
  iterations nor recovered from a caller assertion.
- Parent and unrelated-resource calls remain rejected by the structural
  termination checker.
- The proof remains within the existing checked execution and certificate
  path; no hidden body rerun or C rewrite is introduced.
- `scripts/check.sh` passes.

Related: [termination-ranking-coverage.md](termination-ranking-coverage.md);
[arena-resource-ownership.md](arena-resource-ownership.md).
