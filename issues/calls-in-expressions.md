# Allow function calls in expression position

Found by the 2026-09-01 kernel audit at cb034b21.

Calls exist only as `f(args);` statements or as direct assignments
`x = f(args);` (`src/languages/c/syntax.rs:1120-1124` dispatching to
`:1322-1329`, `:1149-1157`, `:1239-1251`). `parse_postfix` handles only `[` and `->` (`:1639-1663`) and
`parse_primary` maps identifiers to variables (`:1740-1741`), so
`return f(x);`, `g(f(x))`, `if (f(x))`, and calls in conditions or arguments
all fail to parse. The workaround, a named temporary, is a source rewrite of
nearly every real function (`mdtests/c_local_named_result_across_calls.md`
exercises the required pattern).

## Violated invariant

Click should accept a call wherever C allows an expression, lowering it to
the existing call statements with fresh temporaries in a way that preserves
C's evaluation-order constraints, so that `return f(x);` verifies unchanged.

## Intended regression

Mdtests with unchanged C: `return helper(x) + 1;`; `if (is_valid(p)) {...}`;
`total = add(mul(a, b), c);`; `arr[index_of(key)] = 1;`. Each verifies with a
sidecar that applies the callees' contracts. A negative mdtest shows that two
calls in one expression whose relative order is unspecified in C and whose
contracts have overlapping mutable footprints are rejected or both orders are
checked, never silently sequenced.

## Acceptance criteria

- The parser accepts postfix call syntax in expressions.
- Lowering introduces kernel-fresh temporaries and sequences calls into the
  existing `CallAssign` statements; the lowering is documented as
  semantics-preserving under C's sequencing rules, including the
  unspecified-order case.
- Contract and resource transfer at each lowered call is unchanged.
- Diagnostics report the original expression position, not the synthesized
  temporary.
- `scripts/check.sh` passes.
