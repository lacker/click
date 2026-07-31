# Parser ergonomics residue

Status: done (2026-07-30) — both residual items were stale; the one real
limitation found is parked as C5 in ../language-proposals.md.
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

## mdtest de-padding — done

The "49 of 269" figure counted mdtest files containing *any* `else` in a
C block (the real pre-change number was 50 files), not no-op padding.
The actual padding was **22 `else` blocks across 11 files**, all of the
self-assignment shape `p[j] = p[j];` / `count = count;`. All 22 removed,
in three commits:

- sort3 / compare_swap2 family — 10 blocks, 5 files
- bubble sort family — 5 blocks, 4 files
- byte_slice_stdlib + pure_click_functions — 6 blocks, 2 files

**40 `else` blocks left alone**, every one of them genuinely assigning a
value or returning (`y = 0;`, `return 0;`, `selected = right;`,
`i = i + 1;`, `tmp = 0;`, …). Nothing was left alone merely for
statement renumbering: none of the 11 padded files used `statement(N)`
or positional `requirement N` references, which was checked before
touching them. Many of the survivors live in tests whose whole point is
branch behaviour (proof_advance_*, execute_step_nested_branches).

Not padding, deliberately untouched: the Click function expression
`if x == y { 1 } else { 0 }` in pure_click_functions.md (a click block,
not a C block), and examples/owned-vector/vector_replace_if.c, whose
`else` calls `vector_set` with a different argument.

Side effect: `cargo test --test mdtests` dropped from ~16 s to ~10 s
with the dead statements gone.

Detection gotcha for whoever repeats this: `"```click".startswith("```c")`
is true, so a naive fence check treats Click blocks as C. Match the fence
info string's first token against exactly `c`.
