# Deeply parenthesized contract expressions can overflow the parser stack

The Click parser treats a parenthesized contract expression by re-entering the
full proposition parser. Each level therefore adds the complete proposition
and expression-precedence call chain to the native stack. A valid theorem
requirement containing roughly 31 nested parentheses around an arithmetic
expression can abort the process with a stack overflow instead of parsing or
returning a bounded diagnostic.

This was exposed while building the surface-spelling scaling gate. LLDB showed
the repeating cycle
`parse_proposition` -> `parse_proposition_atom` ->
`parse_contract_expression` -> `parse_contract_primary` once per parenthesis.
The scaling fixture now uses shallow spellings because parser nesting is a
different axis; this issue preserves the independent defect.

## Regression design

Generate a valid contract expression with geometrically increasing parenthesis
depth and parse it in-process. Parsing must either succeed with work linear in
the token count or return an explicit enforced nesting-limit diagnostic. It
must never overflow the native stack. Keep a shallow mixed proposition and
contract-expression case to preserve the intended ambiguity resolution.

## Acceptance criteria

- Valid nesting at the documented supported depth parses successfully.
- Excessive nesting returns a deterministic source diagnostic before stack
  exhaustion.
- Parser work is linear in the consumed token count.
- No test relies on increasing a thread stack or subprocess crash isolation.
