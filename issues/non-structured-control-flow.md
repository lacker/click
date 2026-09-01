# Model break, continue, do-while, switch, and goto

Found by the 2026-09-01 kernel audit at cb034b21.

`parse_statement` (`src/languages/c/syntax.rs:1080-1263`) knows only
`return`, `if`, `while`, `for`, and `free`. `break;` fails as "expected
statement, got identifier `break`"; `switch (x) {` parses `switch` as a call
statement and dies on the `{`; `do` and labels are unparseable. The kernel
`CStatement` enum (`src/kernel/primitives.rs`) has no Break, Continue,
Switch, Goto, or DoWhile variants, so a loop that exits early has no faithful
representation and restructuring it is exactly the source rewrite the
project doctrine forbids. No mdtest or example uses any of these.

## Violated invariant

Click should give every structured and semi-structured control-flow statement
of the C0 subset its C semantics, so that a loop with `break` or `continue`,
a `do`-`while`, or a `switch` over an integer verifies without rewriting.

## Intended regression

Staged mdtests, each an unchanged C function with a sidecar proof:

1. `while (i < n) { if (a[i] == key) { break; } i = i + 1; }` with a
   postcondition that `result` is the first matching index or `n`.
2. The same loop using `continue` to skip elements.
3. `do { i = i + 1; } while (i < n);` with a loop invariant that is checked
   after the first iteration.
4. `switch (kind) { case 0: ...; break; case 1: ...; break; default: ...; }`
   including fallthrough between two cases.
5. `goto` to a cleanup label at the end of a function (the error-path
   cleanup idiom), with resources released on both the normal and the goto
   path.

## Acceptance criteria

- `CStatement` gains the needed forms (or a lowering to existing forms that is
  proven semantics-preserving in a doc and pinned by tests); loop rules
  handle exit and continue edges so invariants are checked at every back edge
  and exit.
- The surface `loop` tactic and loop summaries accept bodies with `break` and
  `continue`.
- `switch` lowers with C's fallthrough semantics; `goto` is supported at least
  for forward jumps to a label at function scope, with a diagnostic for
  unsupported jump shapes.
- The five mdtests pass; `scripts/check.sh` passes.

Related: [c-syntax-conveniences.md](c-syntax-conveniences.md) for
`else if` and unbraced bodies, which need only the parser.
