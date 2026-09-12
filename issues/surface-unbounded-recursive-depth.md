# Bound structural nesting beyond parentheses without aborting the CLI

P2 tooling reliability: small non-parenthesized inputs overflow the main
thread stack. Reproduced at `3ad0d2e1` in the default debug build on macOS.

## Violated invariant

Input beyond a supported structural limit must produce a prompt, bounded,
source-located diagnostic. Native recursion must not abort the verifier
before its work or command limits can report a failure.

`validate_parenthesis_nesting` in `src/surface/parser.rs` bounds only
simultaneously open parentheses; a separate limit covers expression matches.
`parse_proposition_implies` and `parse_proposition_not` recurse without a
corresponding structural check. Quantifier bodies recurse through braces,
and long operator chains can create deeply nested ASTs that later consumers
or destructors visit recursively. A parser-only patch must also account for
those downstream paths.

## Small reproduction

Generate `depth.click`:

```python
from pathlib import Path

source = ('theorem depth() { requires ' + 'not ' * 128 +
          '0 == 0; ensures 0 == 0 by { normalize(); } }')
Path('depth.click').write_text(source)
```

The source is only 583 bytes, contains a true precondition, and has no nested
parentheses. `click verify depth.click` aborts with:

```text
thread 'main' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

Python observes return code `-6` (SIGABRT), rather than an ordinary Click
failure. With 32 negations, the same theorem verifies. The review also
reproduced aborts with 512 `implies` links, 1024 zero terms joined by `+`,
and 64 nested `forall` bodies whose parenthesis nesting is only one.
Overflow thresholds depend on the platform and build; tests must not rely
on these particular thresholds. Process checks after the crash suite found
no remaining verifier workers.

## Acceptance criteria

- Every reproduction family either verifies or returns a bounded,
  source-located supported-depth error; none aborts, panics, hangs, or leaves
  workers behind.
- Test deterministic structural boundaries while keeping shallow valid
  inputs working, rather than depending on the host's stack-overflow depth.
- Cover unary, right-associated and left-associated operators, braces,
  brackets, and nested proof constructs through parsing, validation,
  printing, and destruction where applicable.
- Apply the guarantees to the public surface API and the verify, profile,
  expand, and audit paths without increasing stack sizes or tactic limits.
- `scripts/check.sh` passes.
