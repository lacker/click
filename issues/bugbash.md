# Bug bash: open tooling failures

Three remaining tooling failures are tracked here. They reject supported inputs
or expose verifier reliability gaps.

This is deliberately a bundle rather than one file per problem, so the set
stays together while it is triaged. **Split it up as work starts**: when a
root cause is picked up, move its section into its own `issues/<name>.md`, add
the Open-list line, and delete the section here. Delete this file when the
last section is gone.

The following tooling failures block use rather than admitting false claims.
Several entries say what *not* to do: those directions were built and
measured, and each broke sound proofs elsewhere or lost a capability the tree
uses. Read them before starting.

## 1. `--changed-since` cannot resolve project-local headers

A project with
`cap.h`, `m.c` containing `#include "cap.h"`, and a sidecar verifies with
`click verify`, but `--changed-since HEAD` (and `--explain`) fails with
`cannot resolve local include cap.h as cap.h in the source bundle`, with no
change in the tree. Incremental mode builds its source bundle without headers.
Acceptance: incremental verification of a project with local headers works, and
a header edit selects the functions whose translation units include it.

## 2. `execute()` emits a certificate the checker rejects

This occurs for `break` inside an `if` inside a nested `while`, in the same
class as item 1.

## 3. Panic (`unreachable!`) when a local struct initializer zero-fills a
`float`/`double` field

A crash, not a wrong answer. Acceptance: the initializer is either supported
or rejected with a source-positioned diagnostic.

---

## Checked and found sound

Recorded so the next pass does not re-cover this ground. Each was probed
directly against the release binary with claims that are false under C; each
was correctly rejected, and the corresponding true claims verified.

- Integer operators: signed division truncation and remainder sign, arithmetic
  right shift, `1 << 31` flagged, `INT_MIN / -1` flagged, precedence of `-`,
  `%`, `<<`, and `&` against `==`, chained comparisons, octal literals,
  `~0 == -1`, `(-1) & 255 == 255`.
- Signed/unsigned comparison `-1 < 1u` is false; `int32 + uint32` wraps
  unsigned; concrete `int32 + int64` computes in 64 bits.
- Control flow: `switch` fallthrough and `break` inside a `switch` inside a
  loop, `do ... while` running once, `continue` in `for` running the step,
  short-circuit evaluation with a division by zero on the right, the unselected
  arm of a conditional.
- Undefined behaviour at constant indices: local and global array
  out-of-bounds, uninitialized scalar, pointer, struct-copy and loop-body
  reads, missing return in a non-void function, pointer index scaling overflow.
- Frames: writing a global through a pointer under `immutable`, storing a fresh
  allocation's address into a global under `immutable`, a callee mutating a
  global with the caller claiming it unchanged, and a callback parameter
  shadowing a file-scope function.
- Resources: two `owns` clauses over aliasing arguments are rejected as
  overlapping; `views` and `owns` over the same cell are not assumed separate.
- Floating point with symbolic operands: NaN keeps the third path in
  `a < b` / `b <= a`, `a == a` is not assumed, `a != a` is not assumed false.
- Undefined behaviour inside `requires` is checked as a callee precondition at
  call sites, and an overflowing callee `ensures` instantiation yields no fact.
- Incremental selection re-verifies correctly after a callee contract change, a
  callee body change, a strengthened callee precondition, a caller body change,
  a global initializer change, an extern contract change, a theorem change,
  and a named-contract or algebraic type change.
- Sidecar/C signature mismatches (arity, parameter order, parameter type) and
  missing functions are rejected.
- The proof object and simple tactics: the reviewer assigned to
  `assumption`/`extract`/`rewrite`/`instantiate`/`enumerate`/`contradiction`,
  branch joins and splits, and the fact store produced no reproducible finding.
- The `prove_int32_*` axioms in `src/kernel/api.rs` were checked at their
  boundary values and are sound as stated.

## Ruled out

Reported during the review and refuted on inspection. Do not re-file.

- **An `extern` contract can state a false axiom.** True, and documented:
  `docs/reference/language/c0.md` says an `extern` declaration is applied as an
  explicit assumption. The trusted boundary is the feature.
- **Struct-pointer resource ranges use 4-byte logical units.** An internal
  spelling question, not a claim about C; the reproduction's postcondition is
  true.
- **`choose` witness ids collide with loop-invariant binder ids.** The reported
  route does not exist; the reproduction exits 1, and the "certificate failed
  round-trip validation" message it produces is a rejection, not an acceptance.
- **`click verify` exits 0 on a sidecar with no proof units.** Documented
  behaviour: a sidecar target verifies every claim in that sidecar, and there
  are none.
