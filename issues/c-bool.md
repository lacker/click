# Model C `_Bool` and `bool`

Found by the 2026-09-04 MVR audit. Linux rbtree functions and callbacks use
`bool`, `true`, and `false`. C0 currently models comparison results as `int32`
and has no documented `_Bool` object or conversion semantics.

## Violated invariant

An accepted C boolean must have C's normalized value semantics: conversion to
`_Bool` yields zero or one, boolean objects have the selected ABI layout, and
calls and struct fields retain that type rather than silently becoming an
unrelated integer type.

## Intended regression

An unchanged C fixture defines a `bool` local, parameter, return value, and
struct field; assigns both comparison results and a nonzero integer; and uses
`true` and `false`. Postconditions establish that every stored and returned
boolean is zero or one. Negative coverage rejects an ABI or signature mismatch
with an ordinary integer of a different type.

## Acceptance criteria

- `_Bool` and the configured `bool` typedef parse with explicit size,
  alignment, promotion, assignment, parameter, and return rules.
- Integer and pointer conversions to `_Bool` follow the supported C semantics
  and normalize to zero or one; floating conversions remain with the separate
  floating-point work.
- `true` and `false` have their configured header meaning without requiring
  edits to Linux source.
- Function-pointer signature compatibility distinguishes boolean types where
  the ABI or C type rules require it.
- The rbtree boolean signatures, focused regressions, and `scripts/check.sh`
  pass.
