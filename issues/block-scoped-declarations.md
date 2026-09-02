# Lift the block-scoped declaration restriction

The kernel names local cells as `local:{name}`, so C0 rejects a declaration
that shadows a parameter or an enclosing local. Sibling blocks may reuse a
name, but nested lexical scopes cannot.

## Violated invariant

Click should distinguish objects with different C lexical scopes while keeping
their lifetimes, addresses, and struct-pointee metadata separate.

## Intended regression

An unchanged C function declares an inner `value` that shadows an outer
`value`, takes each address in its own scope, and returns the outer value after
the inner block ends. A negative control confirms that the two addresses are
not conflated.

## Acceptance criteria

- Local identities and struct-layout metadata are scope-indexed rather than
  name-only.
- Address-taking, loop havoc, calls, and diagnostics preserve lexical lifetime.
- The shadowing regressions pass; `scripts/check.sh` passes.
