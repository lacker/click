# Model break, continue, do-while, switch, and goto

Found by the 2026-09-01 kernel audit at cb034b21.

The initial native control-flow slice now models `break`, `continue`, and a
bounded `switch` in the kernel and surface proof path. The remaining gap is
that `do ... while` still has distinct edge semantics that are not preserved by
the current lowering, and labels/goto are unparseable. The switch slice is
currently limited to direct integer or character literal labels in one
compound body; arbitrary constant expressions and nested labels remain future
work.

## Violated invariant

Click should give every structured and semi-structured control-flow statement
of the C0 subset its C semantics, so that a loop with `break` or `continue`,
or a `switch` over an integer verifies without rewriting.

## Intended regression

Staged mdtests, each an unchanged C function with a sidecar proof:

1. `while (i < n) { if (a[i] == key) { break; } i = i + 1; }` with a
   postcondition that `result` is the first matching index or `n`.
2. The same loop using `continue` to skip elements.
3. `switch (kind) { case 0: ...; break; case 1: ...; break; default: ...; }`
   including fallthrough between two cases (`mdtests/c_switch.md`).
4. `goto` to a cleanup label at the end of a function (the error-path
   cleanup idiom), with resources released on both the normal and the goto
   path.

## Acceptance criteria

- `CStatement` gains the needed forms (or a lowering to existing forms that is
  proven semantics-preserving in a doc and pinned by tests); loop rules
  handle exit and continue edges so invariants are checked at every back edge
  and exit.
- The surface `loop` tactic and loop summaries accept bodies with `break` and
  `continue`.
- `switch` has a checked native implementation with C's fallthrough semantics
  for its supported literal-label shape; the remaining switch extensions and
  `goto` need explicit diagnostics and regressions.
- The five mdtests pass; `scripts/check.sh` passes.

Related: [c-syntax-conveniences.md](c-syntax-conveniences.md) for
`else if` and unbraced bodies, which need only the parser.
