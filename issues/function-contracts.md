# Function-pointer contracts: residual gaps

Found by the 2026-09-04 MVR audit; the mechanism landed on 2026-09-11. A
function-pointer value now carries a checked named contract, every indirect
call is justified by that contract alone, and a concrete address is admitted
only by checked refinement. What follows is the residue: verifier gaps and
cleanups the implementation surfaced, each with its reproduction fixture or
the fixture that had to route around it. None is filed separately; split one
out when it is picked up.

## What landed (for orientation)

- Named `contract` blocks; `Name(pointer)` facts indexed by the exact pointer;
  proof-parameter contracts `contract Exact(cell: Counter()) for int32()`.
- Concrete formation at `&f` by an exact-only refinement judgment
  (`prepare_contract_refinement_obligations`, `src/kernel/functions.rs`),
  admitting scalar memory propositions, sequences, resource fields, and
  algebraic values, with a forced instance binding keyed by resource family;
  refusal prints the explicit theorem skeleton
  (`mdtests/c_named_contract_refusal_prints_theorem.md`).
- Explicit routes: `unfold(Name)` theorems; abstract `executes` theorems with
  `ensures Target(cb) as { param: name }`; concrete `executes f(params)`
  theorems (`mdtests/c_contract_executes_concrete.md`).
- Binder transport at ordinary C calls: `step(f(args), { binder: name })`
  and `let name = step(...)` (`mdtests/c_call_binder_transport.md`).
- Bare designator decay and file-scope const callback tables
  (`mdtests/c_callback_bare_designator.md`,
  `mdtests/const_callback_table_dispatch.md`).
- Rotation and callback-table regressions
  (`mdtests/augment_rotate_callback.md`,
  `mdtests/augment_rotate_model_callback.md`,
  `mdtests/rb_augment_callbacks_*.md`).
- Certification failures now report the runtime error and clause index
  instead of "produced no paths"
  (`mdtests/contract_certification_reports_resource_error.md`).

Commits, in landing order: `bdcab487`, `fd679912`, `5400cf07`, `d38cf746`,
`7ff56487`, `f9653202`, `a4aa68c2`, `335027f9`, `548c7b1e`.

## Violated invariant

A call through an abstract function pointer must be checked against an
explicit contract carried by that pointer, and the Linux augmented rbtree's
callback sites must be verifiable in their real shape. The gaps below are
what still stands between the landed mechanism and that shape.

## Gaps that block the rbtree callback sites

**G1. Two indirect calls through one opened callback-suite resource.** With
`owns` footprints on the callback contracts, the second indirect call in a
helper that has done `open(suite(augment)) { ... }` fails with ``cannot verify
call through function pointer `__click_call_result3`: no matching named
contract is available for this value``. One call per opened resource works;
any two of three fields reproduce it; re-opening per call fails at the close
(`the rewritten composite is absent from both resource representations`); and
`views` footprints work for any number of calls, which is why
`mdtests/rb_augment_callbacks_helper.md` ships with no-op footprints. The
Linux erase helper calls `propagate`, `copy`, and `rotate` through one
`const struct rb_augment_callbacks *` with real footprints, so this is the
first thing to fix. Intended regression: the helper fixture with `owns
node->left` on each contract and `ensures node->left == old(node->left)`,
three calls, passing.

**G2. A contract cannot own a segment whose base is loaded through a field
another owned or consumed composite owns.** `requires node->right != 0; owns
pair(node); owns node->right->augmented;` fails certification with `could not
evaluate an owned memory resource segment (resource clause 2 of 2)`, while
`views pair(node)` or owning the two links directly passes. Both rotation
fixtures take the root's link cells and subtree resources separately because
of this. Intended regression: `rotate_left` contracted as `consumes
shape(node); produces shape(result); owns node->augmented; owns
node->right->augmented`.

**G3. A named contract's resource clause cannot read through a parameter.**
`requires old->left != 0; views old->left->augmented;` in `AugmentRotate`
fails to prepare with `missing pure fact: loadable(base=old, bytes=8)`,
because contract clauses are lowered with no facts or resources in scope. A
realistic recompute callback reads its children's augmentation, so this
blocks the stretch form of the rotation fixture. Intended regression: the
rotation fixture with that clause and a `bump` that reads
`old->left->augmented`.

## Gaps that shaped fixtures but are not on the rbtree path

**G4. Suite resources over a file-scope const table.** `fold(suite(&table))`
demands ownership of the static block, which nobody holds, so
`mdtests/rb_augment_callbacks_table.md` states the three facts directly with
`views object(augment)`. Relatedly, `object(&static_object)` is not spellable
(`object(...) currently expects a named C struct pointer parameter`), so a
caller cannot state separation between a static table and a parameter block.

**G5. Resource-field requirements match exactly.** `requires first.revision
< 1000` on a callee and `requires c.revision < 999` on the caller fails the
step; identical bounds pass. Two `old()`-relative guarantees across two calls
do not chain (`i2 == i1 + 1`, `i5 == i2 + 1` does not close `i5 == i1 + 2`),
and call successors record no synthesized `old(...)`, so the intermediate
value has no spelling. A grouped `by { ... }` proof declines a `have` between
execution steps.

**G6. Prover gaps met along the way.** `simp` cannot discharge a constructor
disequality (`r.model != Mark::Clear()` from `r.model == Mark::Set()`); does
not orient a pure-function equation across a callback call, so
`mdtests/augment_rotate_model_callback.md` restates the model with an
explicit `rewrite`; and does not prove `0 <= a, 0 <= b, defined(a + b) ⊢
0 <= a + b`.

**G7. Undeclared identifiers in value position** are not rejected at parse
time in general; they reach the kernel as unbound variables and fail as proof
errors. The function-pointer path now says `use of undeclared identifier`;
the general case is untouched because an existing unit test parses
`values[index_of(x)]` with `values` undeclared.

## Diagnostics and cleanups

- `src/surface/diagnostics.rs` renders an available `Contract(p)` fact on a
  symbolic pointer as ``named contract `X` is not established for p`` inside
  "available pure facts", and a missing fact inside a `fold` failure as
  ``function `f` does not satisfy named contract `N` ``, which reads as a
  refused refinement rather than an absent fact.
- The refusal skeleton spells an aggregate-pointer parameter by its pointer
  type because the kernel interface keeps a layout, not a struct tag;
  `struct node*` prints imprecisely.
- Forced binding for automatic formation is keyed by resource family only;
  two binders of one family refuse even when arguments would disambiguate.
- Post instance fields are always fresh after a call or a refinement,
  including for a binder returned unchanged; preservation must be stated.
- The `as`-map rename of target clauses is encoded as a field-free
  `ResourceField` substitution entry guarded by identity
  (`resource_instance_rename_entry` in
  `src/surface/lowering/contract_substitution.rs`); a dedicated substitution
  variant would be cleaner.
- Binder names for call transport live in a parser-side registry keyed by
  callee rather than on `CResourceSpec::Instance::binder`; fold the two
  together. One `produces` binder per callee is supported.

## Acceptance criteria

- G1 fixed with the three-call helper fixture passing under `owns` footprints.
- G2 and G3 fixed with the rotation fixtures rewritten to their natural
  contracts and the child-read form passing.
- The two diagnostic wording defects fixed with fixtures asserting the text.
- Any of G4 through G7 fixed with a regression, or split into its own file
  when picked up.
- `scripts/check.sh` passes.

Related: [struct-model.md](struct-model.md),
[global-variables.md](global-variables.md),
[linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md).
