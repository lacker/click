# Specify external and libc functions without a body

Found by the 2026-09-01 kernel audit at cb034b21.

A call to a function with no C0 body in the project is a
`CRuntimeError::UnknownFunction` (`src/kernel/primitives.rs:760`, raised at
`src/kernel/loops.rs:15` and `:87`, rendered as "unknown function" at
`src/surface/diagnostics.rs:497`).
Before the first implementation slice, there was no extern-contract
mechanism, so `memcpy`, `memset`, `strlen`, `printf`, or any vendored helper
could not appear in verified code. The remaining gap is the standard-library
contract catalog and automatic reporting of external assumptions.
`docs/internals/roadmap.md:163-165` proposes treating `malloc`, `free`,
`memcpy`, `memcmp`, `strlen`, "and friends" as modeled builtins or externally
specified functions; `malloc` and `free` are the only ones modeled today.

## Status

The first implementation slice now supports body-less `extern` function
contracts in sidecars. Their requires, ensures, resource clauses, and mutable
footprints are checked at call sites, while the kernel records the declaration
as an opaque assumption rather than executing a synthesized body. Empty
contracts and callers that cannot establish an external precondition are
rejected. The standard-library contract catalog and dependency reporting for
external assumptions remain open.

## Violated invariant

Click should let a sidecar declare a contract for a function whose body is
not in the project, applied as an opaque rule at call sites with no body
execution, so that real C calling libc and library helpers can be verified
against the callee's specification.

## Intended regression

An mdtest whose C file calls `memset(p, 0, n)` and `strlen(s)` with no
definitions present, verified against sidecar declarations of the form
`extern void memset(uint8* p, int32 v, int32 n) { owns p[0..n]; mutable
p[0..n]; ensures forall (k: int32) { 0 <= k and k < n implies p[k] == v }; }` (in
whatever surface form is chosen). A negative mdtest shows a caller violating
the extern's `requires` is rejected, and another shows that an extern
declared without a contract is rejected rather than assumed to do nothing.

## Acceptance criteria

- Surface Click has a declaration form for external functions carrying
  requires, ensures, resource clauses, and mutable footprints, with no body.
- The kernel installs such a declaration as an opaque rule marked as an
  assumption (an axiom of the project), distinct from a verified rule, and
  `click verify` reports which externs a verified function depends on.
- A standard-library sidecar provides contracts for the libc functions the
  roadmap names; `stdlib/` verification checks each against its stated
  proposition as it does for theorems.
- Opaque-contract eligibility (`proposition_supported_in_opaque_contract` in
  `src/surface/lowering/annotations.rs`) covers the shapes libc contracts
  need.
- `scripts/check.sh` passes.
