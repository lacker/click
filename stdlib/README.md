# Click standard library

`prelude.click` is loaded implicitly with every sidecar and C-free theorem
file. Types, pure functions, and theorems use ordinary Click declarations;
library theorems are checked, not trusted axioms.

The library is checked on its own, like any dependency: `verify_standard_library`
proves every library theorem, and the gate runs it in
`standard_library_theorems_are_proved_by_their_own_entry_point`. Verifying a
sidecar applies library theorems as dependency declarations and proves only
the sidecar's own theorems. Whole-contract certification accepts a pure theorem
only with kernel authority from a checked proof, so a C proof that cites one of
the few library theorems that certification consumes checks that cited theorem
once during its verification.

Keep the public declarations here until Click supports specification imports.
The module/import work is tracked in
[`issues/specification-imports.md`](../issues/specification-imports.md).

For a library addition:

- Put positive and negative client examples in `mdtests/`. List clients live
  in `stdlib_list*.md` and should use the implicit library, not redeclare it.
- Add a checked use to `mdtests/stdlib_every_symbol.md`.
- Copy the exact declaration into `docs/reference/library/index.md` and add
  its entry to `docs/reference/inventory.toml`. The documentation gate checks
  these against the source.
- Run a focused fixture check, then the full `scripts/check.sh` gate. Add
  expansion coverage when exercising a new proof path.

Generic proofs are verified for each concrete instance when used. Exercise
different element families explicitly; a test at `int32` does not check every
possible instantiation. The list fixtures cover scalar and pointer elements
and append over nested lists. The library reference documents current limits.
