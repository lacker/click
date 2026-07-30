# Parser ergonomics residue

Status: open
Claimed:

Scope (design-review item 4 residue): comments, unary minus, and
declaration initializers were fixed earlier. Verify current status of
the remaining two and fix if small; otherwise write up why they belong
to the language arc:
- required-else (every `if` demands an `else`; 49 of 269 mdtests carry
  no-op else padding),
- `a->b->c` chains (field struct-types parsed then discarded, old
  syntax.rs:515).
Error messages should name the restriction when a construct is
rejected.

Done when: each is either fixed with mdtests (and no-op else padding
removed from a few tests as proof) or documented as parked with a
pointer in ../language-proposals.md.
