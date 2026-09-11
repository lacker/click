# Function-pointer contracts: residual gaps

Found by the 2026-09-04 MVR audit; the mechanism landed on 2026-09-11. A
function-pointer value now carries a checked named contract, every indirect
call is justified by that contract alone, and a concrete address is admitted
only by checked refinement. What follows is the residue: the verifier gaps
and cleanups the implementation surfaced that belong to this mechanism. Gaps
that belong elsewhere have been moved: the `simp` and arithmetic gaps to
[simplify-step.md](simplify-step.md) and [arithmetic.md](arithmetic.md), and
resources over file-scope callback tables to
[global-variables.md](global-variables.md).

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
  `mdtests/rb_augment_callbacks_*.md`), including three indirect calls with
  `owns` footprints through one opened suite
  (`mdtests/rb_augment_callbacks_helper_owns.md`).
- Certification failures report the runtime error and clause index instead
  of "produced no paths"
  (`mdtests/contract_certification_reports_resource_error.md`).

Commits, in landing order: `bdcab487`, `fd679912`, `5400cf07`, `d38cf746`,
`7ff56487`, `f9653202`, `a4aa68c2`, `335027f9`, `548c7b1e`, `5bbee2f1`,
`16fe83e4`.

## Violated invariant

A call through an abstract function pointer must be checked against an
explicit contract carried by that pointer, and the Linux augmented rbtree's
callback sites must be verifiable in their real shape. R1 and R2 below are
what still keep the rotation fixtures from their natural contracts; the rest
are correctness of diagnostics and code quality.

Conventions for every item: work in a task worktree; never change fixture C
to make a proof pass; the gate is `scripts/check.sh` judged from its exit
status; do not create new issue files.

## R1. Contract resource clauses see the whole clause set

**Gap.** A contract cannot own a segment whose base is loaded through a field
that another owned or consumed composite in the same contract owns:

```click
resource pair(node: struct node*) { owns node->left; owns node->right; }
void probe(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    owns pair(node);
    owns node->right->augmented;
}
```

fails certification with `could not evaluate an owned memory resource segment
(resource clause 2 of 2)`, while `views pair(node)` or owning the two links
directly passes. Requirements already read through folded composites
(`requires node->right != 0` next to `consumes tree(node)` works, see
`tree_rotate_left` in `examples/binary-tree/binary_tree.click`); resource
clauses do not. Both rotation fixtures take the root's link cells and subtree
resources separately because of this.

**Decision.** Resource clauses are evaluated against loadability supplied by
the whole clause set, regardless of clause order, the way requirements are.
A base load in one clause may read a cell any other clause owns or views,
including a cell inside a folded composite. A dependency cycle between
clauses is refused with a diagnostic naming both clauses; no clause is
evaluated twice.

**Where.** `evaluate_function_resource_context` and the entry-state
construction in `src/kernel/functions.rs`; contract certification in
`src/kernel/api/contract_certification.rs`. Compare how
`c_function_entry_state` gives requirements their loadability.

**Regressions.** `mdtests/contract_owns_through_composite_field.md` (pass):
the `probe` above, plus a body that writes `node->right->augmented`.
`mdtests/contract_owns_through_composite_field_rejects_cycle.md` (fail):
two clauses each needing the other's cell. Rewrite
`mdtests/augment_rotate_callback.md` and
`mdtests/augment_rotate_model_callback.md` so `rotate_left` is contracted as
`consumes shape(node); produces shape(result); owns node->augmented; owns
node->right->augmented;` (model form: `consumes t: tree_at(node); produces
r: tree_at(result); ...`), keeping their C verbatim and their verdicts.
Update `mdtests/contract_certification_reports_resource_error.md` to a
repro that still fails after this change, or retarget its message.

## R2. Named contracts are prepared with an entry state

**Gap.** A named contract's resource clause cannot read through one of its
own parameters: `requires old->left != 0; views old->left->augmented;` in
`AugmentRotate` fails with `could not prepare named contract 'AugmentRotate':
missing pure fact: loadable(base=old, bytes=8)` and empty fact and resource
lists. C function contracts get an entry state built from their own clauses;
named contracts are lowered in a bare state. A realistic recompute callback
reads its children's augmentation, so this blocks the natural rotation
fixture.

**Change.** Prepare a named contract the way a C function contract is
certified: build its entry state from its parameters and clauses so that
loads through parameters and through clause-supplied cells are justified,
then lower requirements, resources, and guarantees in that state. After R1,
the same whole-clause-set rule applies.

**Where.** Named contract preparation (search for "could not prepare named
contract" in `src/surface` and follow it into the kernel).

**Regressions.** `mdtests/augment_rotate_callback_child_read.md` (pass): the
chunk 3 C verbatim, `AugmentRotate` with `requires old->left != 0; views
old->left->augmented;`, and a `bump` that reads `old->left->augmented` into
`new->augmented`; a `reset` that does not read it must still refine.
`mdtests/named_contract_rejects_unjustified_parameter_read.md` (fail): the
same clause without the `old->left != 0` requirement.

## R3. A `have` between execution steps in a grouped proof

**Status: landed** as `7b0d94a2`. The `have` placement already worked at
HEAD; the real gap was `arithmetic() using` as a grouped-proof closer,
which is now accepted post-execution and refused mid-execution with a hint
pointing at `have`. Regressions `mdtests/c_call_binder_transport_tighter_bound*.md`
and `mdtests/c_grouped_contract_arithmetic_closer*.md`.

**Gap.** A grouped `by { ... }` contract proof declines a `have` placed
between two execution steps ("nested `have`") and a top-level `arithmetic()
using`, while a `have` after `execute()` is accepted. A per-clause `ensures
... by { ... }` is not a workaround because `owns c: R()` desugars to a
sibling `ensures` whose default proof re-executes the call with no binder
map. This is what makes a callee with `requires first.revision < 1000` un-
callable under a caller's `requires c.revision < 999`: the exact-route policy
on resource-field requirements is deliberate, and the `have` that bridges
the bound has nowhere to go.

**Change.** Allow `have` (and `arithmetic() using`) at any point of a grouped
proof between execution steps, with the same scoping as after `execute()`.

**Regressions.** `mdtests/c_call_binder_transport_tighter_bound.md` (pass):
the `increment`/`advance` fixture from `mdtests/c_call_binder_transport.md`
with the caller bound `< 999` and a `have c.revision < 1000 by { simp(); }`
before the step. A negative fixture where the `have` is wrong.

## R4. Undeclared identifiers are rejected at parse time

**Status: landed** as `a9c45ae5`.

**Gap.** A never-declared identifier in a value position resolves to itself
and reaches the kernel as `unbound variable`, failing as a proof error. The
function-pointer argument path now reports `use of undeclared identifier`;
the general case does not, because
`languages::c::tests::c0_syntax_lowers_calls_in_expression_position` parses
`return values[index_of(x)];` with `values` undeclared.

**Change.** Reject any undeclared identifier in a value position at parse
time with `use of undeclared identifier`, and declare `values` in that unit
test. Keep the cross-translation-unit call case working (`f(x)` where `f` is
defined in another source).

**Regression.** `mdtests/undeclared_identifier_rejected.md` (fail) and a
unit test for the call case.

## R5. Diagnostics that read backwards

**Status: landed** as `522b17b5`.

`src/surface/diagnostics.rs` renders an available `Contract(p)` fact on a
symbolic pointer as ``named contract `X` is not established for p`` inside
"available pure facts", and a missing fact inside a `fold` failure as
``function `f` does not satisfy named contract `N` ``, which reads as a
refused refinement rather than an absent fact. Print an available fact as
``named contract `X` holds for p`` and a missing concrete fact inside a fold
as ``no `N(&f)` fact is available; apply a refinement theorem or pass `&f`
where `N` is required``. Regressions: one fixture asserting each text.

## R6. Skeleton spelling for struct pointers

**Status: landed** as `b11631bc`; the surface `PredicateEnvironment` is
threaded to the diagnostic and the kernel stores no tag.

The refusal skeleton spells an aggregate-pointer parameter by its pointer
type because the kernel interface keeps a layout, not a struct tag, so
`struct node*` prints imprecisely. **Decision:** do not carry tags into the
kernel for this; the skeleton printer recovers the tag from the surface
declaration of the target contract (its C signature is available where the
diagnostic is rendered). Regression: a variant of
`mdtests/c_named_contract_refusal_prints_theorem.md` over `struct node*`
parameters asserting the exact spelling, and a round-trip variant like
`mdtests/c_named_contract_refusal_theorem_roundtrip.md`.

## R7. Cleanups

**Status: landed** as `570ac8a0`: `ContractSubstitutions` with an
`InstanceRename` map replaces the sentinel (which also removes a latent
keyspace collision); the parser binder registry stays as the single index
with the kernel field copied from the same clause binding.

- The `as`-map rename of target clauses is encoded as a field-free
  `ResourceField` substitution entry guarded by identity
  (`resource_instance_rename_entry` in
  `src/surface/lowering/contract_substitution.rs`). Give the substitution
  map a dedicated rename variant so no sentinel shape is needed.
- Binder names for call transport live in a parser-side registry keyed by
  callee (`callee_resource_binders` in `src/surface/parser.rs`) rather than
  on `CResourceSpec::Instance::binder`; read the field and drop the registry.
- Forced binding for automatic formation is keyed by resource family only;
  leave as is unless a fixture needs argument disambiguation, and say so in
  the reference if it stays.

No behavior change; existing fixtures are the regression.

## Acceptance criteria

- R1 and R2 landed with the rotation fixtures in their natural contracts and
  the child-read form passing.
- R3 through R6 landed with their fixtures.
- R7 landed with no fixture changes.
- `scripts/check.sh` passes; then delete this file and its line in
  `issues/README.md`.

Related: [struct-model.md](struct-model.md),
[global-variables.md](global-variables.md),
[linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md).
