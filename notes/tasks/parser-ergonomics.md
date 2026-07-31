# Parser ergonomics residue

Status: open
Claimed: worktree-agent-ae75bc92435409231 2026-07-30

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

## required-else: STALE (verified 2026-07-30, prior agent)

`src/lang/c/syntax.rs` ~line 1046 parses `else` as optional and
substitutes `C0Statement::Skip`. A bare `if` with no `else` verifies
clean end to end; mdtests/c_if_without_else.md covers it. The 49 padded
mdtests are historical residue, not a language requirement — de-padding
is bookkeeping (see below).

## `a->b->c` chains: STALE (verified 2026-07-30)

The claim that field struct-types are parsed then discarded is false
today. `C0Expression::Field` carries `field_struct_name`
(src/lang/c/syntax.rs:141) and `resolve_field_access` (:1495) reads it
off a `Field` base, so chains resolve to arbitrary depth.

Empirical repro (scratch dir outside the repo):

```
$ cat chain.c
struct inner { int32 value; };
struct outer { struct inner* in; };
int32 chain_get(struct outer* o) { return o->in->value; }
$ cargo run --quiet --bin click-verify -- chain.click
$ echo $?
0
```

Negative control (same file, `ensures result == 12345;`) exits 1, so the
pass is real. Reads, writes (`o->in->value = 5;`), and a three-deep
chain (`r->mid->leaf->value`) all verify. Covered by
mdtests/c_chained_field_access.md.

### One real limitation found, parked as C5

The residue is on the *contract* side, not the parser: an `owns` whose
place base is a doubly-indirect load is rejected by lowering —

```
could not lower `nested` resource: segment base did not evaluate to a
pointer
```

(src/lang/click/lowering.rs:3960). Workaround, and the better idiom:
compose nested resources so each indirects once. Written up as C5 in
../language-proposals.md. Out of this task's lane (lowering.rs).

### Error messages that name their restriction

- Chaining through a non-struct field already said
  ``cannot access field `value` through a non-struct-pointer
  expression`` with the right column. Left alone.
- Two functions in one C file used to die with the generic
  ``expected end of input, got Ident("int32")``. Now names the rule:
  ``each C source file holds exactly one function; put the next
  definition in its own file and add another `verifying` line (got
  identifier `int32` after the end of `one`)``
  (`expect_end` takes the function name; src/lang/c/syntax.rs:1596).

## mdtest de-padding

See the commit series on this branch. Padding of the shape
`else { p[j] = p[j]; }` removed where the `else` branch is a genuine
no-op; left alone where removal renumbers statements that a proof script
addresses positionally (`statement(N).entry`), or where the `else`
assigns something real.
