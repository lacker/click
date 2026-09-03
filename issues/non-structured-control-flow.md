# Preserve structured loop exits and model do-while

Found by the 2026-09-01 kernel audit at cb034b21.

The initial native control-flow slice now models `break`, `continue`, and a
bounded `switch` in the kernel and surface proof path. The remaining gap is
that `do ... while` still has distinct edge semantics that are not preserved by
the current lowering. `continue` in a `for` loop is also rejected because its
edge must run the update clause before testing the condition again. Goto and
labels are tracked separately in [goto.md](goto.md).

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
4. `do { body; } while (condition);` with a `continue` edge to the condition
   and a `break` edge to the following statement.

## Acceptance criteria

- `CStatement` gains the needed forms (or a lowering to existing forms that is
  proven semantics-preserving in a doc and pinned by tests); loop rules
  handle exit and continue edges so invariants are checked at every back edge
  and exit.
- The surface `loop` tactic and loop summaries accept bodies with `break` and
  `continue`.
- `switch` has a checked native implementation with C's fallthrough semantics
  for its supported literal-label shape; its remaining extensions have
  explicit diagnostics and regressions.
- `do ... while` preserves its one initial body execution and distinct
  condition, `break`, and `continue` edges; `for` `continue` reaches its step.
- The five mdtests pass; `scripts/check.sh` passes.

Related: [c-syntax-conveniences.md](c-syntax-conveniences.md) for
`else if` and unbraced bodies, which need only the parser.
