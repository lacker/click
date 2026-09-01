# Model file-scope objects, statics, and string literals

Found by the 2026-09-01 kernel audit at cb034b21.

There are no global or static variables, no static storage, and no string
literals. The grammar admits only struct declarations and one function
(`src/languages/c/syntax.rs:806-830`); `"` is an unexpected character
(`syntax.rs:1945-1972`). `docs/internals/roadmap.md:87-89` lists "char and
string literal support: null-terminated byte arrays, read-only static
storage" and `:96-97` lists globals as remaining. Even once parsed, the
contract language has no story for globals: mutable footprints, initial
values, and initialization order are not expressible, and the `cstr`
predicate layer exists only on the spec side over uint8 buffers.

## Violated invariant

Click should model objects with static storage duration (globals, `static`
locals, string literals) as memory that exists at function entry, with
contracts able to name them in footprints and postconditions, so that real C
that keeps state in globals or passes literal strings can be verified.

## Intended regression

Staged mdtests:

1. A file-scope `int32 counter;` read and incremented by a function, with
   `mutable counter` and `ensures counter == old(counter) + 1`.
2. A `static int32 calls;` inside a function body with the same contract.
3. A function returning a string literal (`return "ok";`) with a postcondition
   that the result is a read-only null-terminated byte array with
   `cstr_len(result, 2)` (three bytes of storage including the terminator;
   `cstr_len` is defined in `stdlib/prelude.click`).
4. A negative test: a function that writes to global state not named in its
   `mutable` clause fails effect certification.

## Acceptance criteria

- The parser accepts file-scope declarations with optional initializers,
  `static` locals, and string literals.
- The kernel models static storage as blocks present in the entry state,
  with a documented identity and initialization rule; string literals are
  read-only blocks and stores to them are undefined behavior.
- Surface Click can name globals in `requires`, `ensures`, `mutable`, and
  resource clauses, and `old()` applies to them.
- Effect certification treats global writes like any other footprint write.
- `scripts/check.sh` passes.

Related: [multi-function-files-and-headers.md](multi-function-files-and-headers.md).
