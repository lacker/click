# Preserve the type of conditional expressions containing calls

P2: a supported wide integer expression is lowered through an `int32`
temporary and rejected. Reproduced at `3ad0d2e1`.

## Violated invariant

Lowering a conditional expression into lazy branches must preserve its C
result type and associated pointer or function-signature metadata.

The `C0Expression::Conditional` branch in `lower_expression_calls` in
`src/languages/c/syntax.rs` declares its synthesized result with
`C0Type::Int32`, regardless of the conditional's actual type. The issue
appears when a branch contains a call; the value-only expression path does
not require this temporary.

## Small reproduction

`wide.c`:

```c
unsigned long wide(void) { return 4294967296UL; }
unsigned long choose(int flag) { return flag ? wide() : 0UL; }
```

`wide.click`:

```click
verifying "wide.c";
uint64 wide() {
    ensures result == 4294967296 by auto;
}
uint64 choose(int32 flag) {
    requires flag != 0;
    ensures result == 4294967296 by auto;
}
```

`click verify wide.click` exits 1:

```text
`choose.ensures_0` tactic 0: `step()` produced runtime error: type mismatch
```

The first function verifies. On the fixed LP64 target, the conditional
branches both have `unsigned long` type, and the precondition selects the
wide result. The runtime type mismatch comes from the incorrectly typed
generated assignment; this is not a smart-search miss. This reproduction
establishes rejection of valid C, not silent truncation.

The existing short-circuit-call issue concerns `&&`/`||` lowering and does
not cover this conditional result-type defect.

## Acceptance criteria

- Verify the unchanged reproduction using the conditional's proper common
  type for its generated temporary.
- Cover supported wider signed/unsigned integers, floating-point values,
  data pointers, and function pointers, preserving applicable metadata.
- Exercise both selected branches and keep the unselected branch lazy;
  genuinely incompatible conditional types must still fail explicitly.
- Preserve the source expression in the regression rather than rewriting
  it into an explicit `if` or a proof-friendly helper.
- `scripts/check.sh` passes.
