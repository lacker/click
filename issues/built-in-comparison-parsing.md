# Parse built-in expressions consistently on either side of comparisons

P2: documented built-in expressions are interpreted as unknown functions when
placed on the left of a comparison. Reproduced at `3ad0d2e1`.

## Violated invariant

An expression primitive must retain the same meaning in either comparison
operand. Parser dispatch must not reinterpret a built-in expression as a
user function solely because it starts a proposition.

The identifier-call shortcut in `parse_proposition_atom` in
`src/surface/parser.rs` creates `ContractExpression::Call` directly for a
call followed by a comparison. Its exclusion list includes `load_int32`,
`load_uint8`, and two pointer loads, but omits `load_uint32`, `load_int64`,
`load_uint64`, `load_int32_pointer_pointer`, and
`load_uint8_pointer_pointer`, as well as `sizeof`. The ordinary expression
parser recognizes these primitives in `parse_contract_non_match_primary`.

## Small reproduction

`read.c`:

```c
uint64 read(uint64* p) { return *p; }
```

`read.click`:

```click
verifying "read.c";
uint64 read(uint64* p) {
    views p[0..1];
    ensures load_uint64(p) == result;
} by { step(); simp(); }
```

`click verify read.click` exits 1 with
`unknown function 'load_uint64' in ensures clause in 'read'` (the diagnostic
uses backticks). Reverse only the equality to
`ensures result == load_uint64(p);` and verification exits 0. Expansion of
the accepted orientation also succeeds. The C, ownership, and logical claim
are identical; this is a parser defect rather than incomplete proof search.

These loads are listed in `docs/reference/language/grammar.md`, and the
wide scalar loads are described in `docs/reference/language/index.md`.

The same dispatch defect breaks `sizeof` without any C input:

```click
theorem size() {
    ensures sizeof(int32) == 4 by { normalize(); }
}
```

This fails with `unknown function 'sizeof' in ensures clause in theorem 'size'`.
Changing only the equality orientation to `4 == sizeof(int32)` verifies.

## Acceptance criteria

- The unchanged read function and size theorem verify with either equality
  orientation.
- Cover `sizeof` and every typed load on both sides of supported comparisons,
  and within arithmetic and parenthesized expressions.
- Preserve predicate calls and ordinary pure-function applications while
  routing built-in expressions through one authoritative classification.
- Expanded certificates that place a typed load on the left must parse and
  reverify through the ordinary surface grammar.
- `scripts/check.sh` passes.
