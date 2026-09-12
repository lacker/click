# Resolve declared C identifiers before built-in constant spellings

P1: a valid C parameter reference becomes a floating constant, allowing a
false contract to verify. Reproduced at `3ad0d2e1`.

## Violated invariant

Every accepted identifier reference must retain its declared C meaning.
Convenience spellings for library constants cannot override parameters,
locals, or other ordinary identifiers in source that defines no such macro.

In `src/languages/c/syntax.rs`, the primary-expression parser matches
`true`, `false`, `INFINITY`, `NAN`, `INFINITYF`, and `NANF` before consulting
normal name resolution. In particular, it replaces `INFINITY` with a
floating infinity even when a parameter with that name is in scope.

## Small reproduction

`positive.c`:

```c
int positive(int INFINITY) { return INFINITY > 0; }
```

`positive.click`:

```click
verifying "positive.c";
int32 positive(int32 INFINITY) {
    ensures result == 1;
}
```

`click verify positive.click` exits 0 with no precondition. The C function
returns 0 when called with 0; its parameter is an ordinary identifier and
there is no header or macro definition in this translation unit. The proof
instead checks whether positive floating infinity is greater than zero.

The analogous GNU11 program `int identity(int true) { return true; }` also
incorrectly verifies `result == 1`, but the `INFINITY` regression avoids any
language-version distinction about boolean keywords.

## Acceptance criteria

- The exact false-contract reproduction fails, while a correct
  parameter-dependent contract verifies on the unchanged C source.
- Preserve parameter, local, and global bindings for the affected ordinary
  identifier spellings. Keep actual supported header/macro expansion
  authoritative rather than recognizing macro-looking names unconditionally.
- Add regressions across ordinary source loading and compiler-prepared
  imports, preserving the distinction between expanded macros and surviving
  identifier references.
- Do not resolve the failure by renaming the regression's parameter or
  imposing a new reservation on an otherwise valid C identifier.
- `scripts/check.sh` passes.
