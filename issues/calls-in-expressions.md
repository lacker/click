# Allow function calls in expression position

Found by the 2026-09-01 kernel audit at cb034b21.

The first implementation slice now accepts calls in unconditional expression
positions, including return expressions, `if` conditions, nested arguments,
and array indexes. It lowers each call to a fresh temporary and the existing
checked `CallAssign` statement. Calls in loop conditions and conditional
expression branches remain open because they require control-flow-aware
lowering; multiple calls in one unsequenced expression are rejected instead
of being silently sequenced.

Before this slice, calls existed only as `f(args);` statements or as direct
assignments `x = f(args);`. The parser now handles calls in unconditional
expression positions, but lowering still rejects calls in loop conditions and
conditional-expression branches because those forms require control-flow-aware
sequencing. Multiple calls in one unsequenced
expression are rejected rather than silently choosing an evaluation order.
The named-temporary workaround remains necessary for those unsupported forms
(`mdtests/c_local_named_result_across_calls.md` exercises the pattern).

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
