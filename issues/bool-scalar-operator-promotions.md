# Apply Bool integer promotions in ordinary scalar operators

P2: valid `_Bool` arithmetic fails with a kernel type mismatch.
Reproduced at `3ad0d2e1`.

## Violated invariant

Accepted C `_Bool` and `bool` rvalues must undergo the documented integer
promotions before arithmetic, ordering, and bitwise operations. Reading a
boolean object must not turn a well-typed C expression into a runtime error.

`scalar_width` in `src/kernel/eval/operators.rs` recognizes `CValue::Bool`,
but ordinary 32-bit operator matching and eligibility checks omit it.
Affected paths include addition, multiplication, ordering, and subtraction.
Shift operations already handle Bool. The integer promotions are explicitly
promised in `docs/reference/language/c0.md`.

## Small reproduction

`boolean.c`:

```c
int f(void) {
    _Bool b = 1;
    return b + 1;
}
```

`boolean.click`:

```click
verifying "boolean.c";
int32 f() {
    ensures result == 2;
} by { execute(); simp(); }
```

`click verify boolean.click` exits 1:

```text
`f.contract` tactic 0: `step()` produced runtime error: type mismatch
```

A focused kernel execution experiment with the same local `_Bool b = 1`
also rejected `1 + b`, `b - 1`, `b * 2`, `b < 2`, `b / 1`, `b % 2`, and
`b & 1` with `RuntimeError(TypeMismatch)`. As a control, `b << 1` correctly
returned `Int32(2)`. These are evaluation failures before proof reasoning,
not incomplete smart-tactic search.

## Acceptance criteria

- The unchanged C function verifies its true result-2 contract.
- Centralize or consistently apply Bool integer promotions in all affected
  operators, with Bool on either side and with both boolean values.
- Add CLI fixtures and focused operator coverage for arithmetic, ordered
  comparisons, and bitwise operations, retaining appropriate C undefined
  behavior checks such as division by zero.
- Preserve working shifts, boolean normalization, assignments, returns,
  storage, and callback signatures.
- `scripts/check.sh` passes.
