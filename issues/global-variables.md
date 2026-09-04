# Model file-scope objects, statics, and string literals

Found by the 2026-09-01 kernel audit at cb034b21.

The scalar file-scope slice and function-local scalar `static` slice are now
implemented: supported integer globals, compatible `extern` declarations,
exactly one linked definition, literal or zero initialization, shared storage
across calls, `old(global)`, one-cell contract footprints, and stable
function-qualified static locals initialized once per program state. File-scope
`static` objects, other linkage forms, aggregate globals/statics,
initialization ordering, and string literals remain unsupported. The `cstr`
predicate layer still exists only on the spec side over uint8 buffers.

## Violated invariant

Click should model every supported object with static storage duration as
memory that exists at function entry, with contracts able to name it in
footprints and postconditions, so that real C that keeps state in globals or
function-local persistent state can be verified.

## Intended regression

The landed regressions are `mdtests/file_scope_globals.md` for cross-translation
unit state and `mdtests/static_scalar_locals.md` for one-time scalar static
storage. Remaining staged regressions are:

1. A function returning a string literal (`return "ok";`) with a postcondition
   that the result is a read-only null-terminated byte array with
   `cstr_len(result, 2)` (three bytes of storage including the terminator;
   `cstr_len` is defined in `stdlib/prelude.click`).
2. A negative test: a function that writes to global state not named in its
   `mutable` clause fails effect certification.

## Acceptance criteria

- The parser accepts supported scalar file-scope declarations with optional
  literal initializers, `extern` declarations, and rejects duplicate or
  missing definitions across the source bundle.
- The kernel models each linked scalar as a stable `global:<name>` block,
  materialized at entry with its literal initial value or zero, and shares that
  block across function frames.
- Surface Click can name scalar globals in `requires`, `ensures`, `mutable`,
  and resource clauses using their address, and `old()` applies to them.
- A function-local scalar `static` has one function-qualified memory block,
  is initialized only when that block first enters the state, remains shared
  across recursive/nested calls, and is nameable by its owning function's
  contracts.
- Effect certification treats scalar global writes like any other footprint
  write, and static-local writes require the same explicit footprint. File-scope
  static objects, aggregate storage, and string literals remain open.
- `scripts/check.sh` passes.

Related: [multi-function-files-and-headers.md](multi-function-files-and-headers.md).
