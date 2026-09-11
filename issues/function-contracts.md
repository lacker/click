# Give function-pointer values checked named contracts

Found by the 2026-09-04 MVR audit. Linux's augmented rbtree core is generic:
exported functions such as `__rb_erase_color` and `__rb_insert_augmented`
receive an `augment_rotate` callback, and the erase helpers call `propagate`,
`copy`, and `rotate` through a caller-supplied
`const struct rb_augment_callbacks *`. Verifying those functions modularly
requires a function-pointer value to carry a checked behavioral contract, and
every indirect call to be justified by that contract alone.

The mechanism is landed and is not in question. This file is now a work
outline: a short summary of what exists, then the remaining chunks in the order
they should be done, each written so an agent can act on it alone.

## Violated invariant

A call through an abstract function pointer must be checked against an
explicit contract carried by that pointer. Signature compatibility alone
cannot justify its result, memory effects, resource transfers, or preservation
of the rbtree invariant.

## What already exists

Read these before starting any chunk; do not re-implement them.

- **Named contracts.** A top-level `contract T Name(params) { ... }` block
  declares requirements, guarantees, resources, and footprint with no C body.
  `Name(pointer)` is a proposition indexed by the exact symbolic pointer; it
  authorizes an indirect call through a parameter or a struct field and is
  never inferred from a signature or a project scan. Positive shapes:
  `mdtests/c_named_function_contract.md`,
  `mdtests/c_named_function_contract_fields.md`,
  `mdtests/c_named_function_contract_pipeline.md`.
- **Resource proof parameters.** A contract that touches a resource instance
  with fields declares it in a parameter list:
  `contract Exact(cell: Counter()) for int32() { owns cell; ... }`. Instances
  are passed explicitly and positionally: `step(Exact(first))` at a call site
  binds `cell` to the caller's `first`. Nothing is matched by binder name or
  by position in a clause list. See `mdtests/contract_resource_parameters.md`
  and `mdtests/contract_resource_call_transport.md`.
- **Concrete-pointer formation.** Passing `&f` where `Name(callback)` is
  required checks that `f`'s verified contract refines `Name`. The judgment is
  `prepare_contract_refinement_obligations` in `src/kernel/functions.rs`: one
  symbolic entry memory, one footprint-havoced post memory, and the implication
  `target_requires implies (source_requires and (source_ensures implies
  target_ensures))`, plus resource framing
  (`framed_resource_transition_refines`) and footprint containment
  (`mutable_footprint_is_compatible`). The failure diagnostic is
  ``function `f` does not satisfy named contract `Name` ``. This route
  refuses any contract with proof parameters
  (`has_compatible_signature_and_resource_vocabulary` in
  `src/kernel/primitives/contracts.rs`).
- **Explicit refinement theorems.** `theorem t() { ensures Name(&f) by {
  unfold(Name); ... } }` proves refinement with ordinary tactics and
  `apply(t())` introduces the fact at a call site. Surface entry:
  `verify_contract_refinement_theorem` in `src/surface/proof/pure_theorems.rs`.
- **Execution theorems.** `theorem t(cb: T (*)(...)) executes cb(params) {
  requires A(cb); ensures B(cb) by { step(A); ... } }` proves one contract
  implies another by running one arbitrary call. `step(A(instance))` passes
  an instance into the source's proof parameter. Checker:
  `verify_execution_theorem` in
  `src/surface/proof/pure_theorems/execution_theorems.rs`; documented under
  "Callback execution theorems" in `docs/reference/language/index.md`.
- **What refinement admits today.** Scalar comparisons, `defined`,
  quantifiers, connectives, and finite sequence comparisons over loads from
  current and function-entry memory. Owned and viewed memory ranges, unit and
  symbolic-quantity abstract tokens, and folded composites, with an inferred
  frame. Unguarded and load-free-guarded footprints. The exact filters are
  `spec_proposition_supports_stateful_memory_refinement` and
  `resource_spec_supports_framed_refinement` in `src/kernel/functions.rs`.

Two known holes shape the order below. First, the execution-theorem checker
makes the target contract's proof-parameter names silently lexical inside the
proof block, so `step(Exact(counter))` uses a name nothing introduced. Second,
an ordinary C call to a function whose sidecar has instance binders such as
`owns first: Counter();` is rejected outright with "calls with named resource
instances require checked binder transport, which is not supported yet"
(`src/kernel/functions.rs`, near the top of
`execute_verified_function_templates`). Every modeled-resource function is
therefore verifiable but uncallable.

Conventions for every chunk below:

- Work in a task worktree; integrate only a green commit (see `CLAUDE.md`).
- Mdtests are Markdown files in `mdtests/` with ` ```c filename=x.c `,
  ` ```click `, and ` ```expect ` blocks. `expect` is `pass` or
  `fail: <substring of the diagnostic>`. Run one with
  `MDTEST_FILTER=<name> cargo test --test mdtests`; the gate is
  `scripts/check.sh`, judged from its `CHECK EXIT` line.
- Never change the C of a fixture to make a proof pass. If a proof cannot be
  written, that is a verifier gap: stop and report it.
- Do not create new issue files. Report findings in the hand-off instead.

## Naming rule adopted for chunks 4 through 6

Names enter an `executes` proof block in exactly three ways, all of them
introductions of new names:

- `executes f(int32* state)` introduces the call's C parameters;
- `ensures Target(...) as { slot: name }` introduces one arbitrary instance
  per proof parameter of the target contract, keyed by the contract's
  parameter name;
- `let name = step(...)` introduces an instance the callee `produces`.

Everything else consumes names that already exist. Passing an instance into a
named contract is positional, `step(Exact(k))`, because the contract has a
declared parameter list. Passing instances into a C function's binders uses a
map, `step(increment(state), { first: k })`, because those binders live in
`owns`, `consumes`, and `produces` clauses rather than a signature. The map
spelling is the one `fold(tree(p), { model: m }, { left: l, right: r })`
already uses for child slots, and `as { ... }` is the keyword `unfold(root)
as { left: l, right: r }` and `induct(n) as ih` already use to introduce
names.

## Chunk 1: bare function designators

**Status: landed** as `bdcab487`. A bare designator needs a declaration in
its own translation unit, matching C; `&f` does not.

**Gap.** C decays a bare function name to a pointer, and Linux passes
callbacks that way: `__rb_insert(node, root, dummy_rotate)`. Click only forms
a function address after `&`. This fails to parse today:

```c
int32 caller() { return apply(compare, 40, 2); }
```

with `expected a compatible function pointer`.

**Where.** `src/languages/c/syntax.rs`. The `&name` case builds
`C0Expression::FunctionAddress` in `parse_unary` (search for
`FunctionAddress(` near the `Token::Amp` arm). Call arguments are checked by
`validate_function_pointer_value`, which accepts `FunctionAddress` and
rejects anything with no known signature.

**Change.** When an identifier is parsed as a primary expression, is not a
declared variable in scope (`self.variable_types` after `resolve_name`), is
not out of scope, and resolves to a known function, produce
`C0Expression::FunctionAddress(self.resolve_function_name(&name))`. Apply
this uniformly so `f` and `&f` are the same expression everywhere a value is
expected: call arguments, assignment to a function-pointer local or field,
struct initializers, and `return`. Do not treat a bare name as an address in a
call position (`f(x)` stays a call).

**Regressions.**

- `mdtests/c_callback_bare_designator.md` (pass): a copy of
  `c_named_function_contract.md` with `apply(compare, 40, 2)`.
- `mdtests/c_callback_bare_designator_field_store.md` (pass): store a bare
  name into a struct function-pointer field and call through it, mirroring
  `struct_function_pointer_field.md`.
- `mdtests/c_callback_bare_designator_signature_mismatch.md` (fail): the bare
  name of a function with a different signature; expect the existing
  `callback signature mismatch` diagnostic.
- `mdtests/c_callback_bare_designator_undeclared.md` (fail): a bare name that
  is neither a variable nor a function; expect `use of undeclared identifier`.

**Docs.** One sentence in `docs/reference/language/c0.md` where function
pointers are described.

## Chunk 2: file-scope const callback tables

**Status: landed** as `fd679912`. By-value structs with function-pointer
fields now parse everywhere, so a modular contract over such a parameter must
carry named contracts on the fields; that is chunk 8 territory.

**Gap.** Linux declares
`static const struct rb_augment_callbacks dummy_callbacks = { .propagate =
dummy_propagate, .copy = dummy_copy, .rotate = dummy_rotate };` and passes
`&dummy_callbacks`. Click rejects any by-value struct object whose type has a
function-pointer field. This fails to parse today:

```c
struct callbacks { int32 (*add)(int32, int32); };
int32 add(int32 left, int32 right) { return left + right; }
static const struct callbacks table = { .add = &add };
int32 caller() { return table.add(1, 2); }
```

with `struct-by-value currently supports ... contains a function pointer or
unsupported field shape`.

**Where.** The rejection is in `src/languages/c/syntax.rs` (search for the
message text). File-scope and static aggregate objects and their initializers
are collected by the code exercised by
`c0_collects_aggregate_static_initializers` and
`c0_collects_designated_static_aggregate_initializers` in
`src/languages/c/tests.rs`; static address initializers by
`c0_lowers_static_address_initializers_with_pointer_provenance`. Struct
function-pointer fields already carry signature metadata when reached through
a pointer (`issues/struct-model.md`, "modeled function-pointer callback
fields").

**Change.** Treat a function-pointer field like a data-pointer field in the
by-value struct model: eight bytes, copied as a value, retaining its
`C0FunctionPointerSignature`. Allow a function address (`&f` or, after chunk
1, `f`) as a positional or designated initializer for such a field in
file-scope and function-local static objects, checking the signature against
the field. Loading `table.add` or `p->add` where `p` is provably `&table`
must yield the concrete address `&add`, so the call dispatches exactly with no
contract. Writes to a `const` object are already rejected; keep that.

**Regressions.**

- `mdtests/const_callback_table_dispatch.md` (pass): a const table with three
  fields bound to three functions with different behavior, called through
  `table.field(...)` and through a pointer parameter that the caller passes as
  `&table`. Guarantees distinguish the three so a swapped binding would fail.
- `mdtests/const_callback_table_abstract.md` (pass): a function taking
  `const struct callbacks *cb` with `views object(cb)` and
  `requires Add(cb->add)` etc., as in `c_named_function_contract_fields.md`;
  a caller passing `&table` must discharge those facts through concrete
  formation of each field's address.
- `mdtests/const_callback_table_rejects_write.md` (fail): assignment to a
  field of the const table.
- `mdtests/const_callback_table_rejects_signature.md` (fail): an initializer
  naming a function with the wrong signature.

**Docs.** Update the by-value struct sentence in
`docs/reference/language/limitations.md` and the field list in
`issues/struct-model.md`.

## Chunk 3: the rotation regression over memory-only resources

**Status: landed** as `mdtests/augment_rotate_callback*.md`; see the
findings at the end of this section.

This is the first of the two regressions named in the acceptance criteria. It
needs no kernel change; it is a fixture that exercises the existing framing
and footprint rules on a tree. If a step cannot be proved, report the gap
rather than reshaping the C.

**C source.** Fix it before writing any Click and do not edit it afterwards.
Node shape and callback signature follow Linux
(`void (*rotate)(struct rb_node *old, struct rb_node *new)`) without the
parent-color word:

```c
struct node {
    struct node *left;
    struct node *right;
    int32 augmented;
};

struct node *rotate_left(struct node *node,
                         void (*augment_rotate)(struct node *old, struct node *new)) {
    struct node *pivot = node->right;
    struct node *middle = pivot->left;
    node->right = middle;
    pivot->left = node;
    augment_rotate(node, pivot);
    return pivot;
}

void bump(struct node *old, struct node *new) { new->augmented = old->augmented + 1; }
void reset(struct node *old, struct node *new) { old->augmented = 0; new->augmented = 0; }
void clobber(struct node *old, struct node *new) { new->augmented = 0; old->left = 0; }
void steal(struct node *old, struct node *new) { new->augmented = old->augmented; }
```

**Sidecar.** Keep the `augmented` cells outside the shape resource so the
callback can own them while only viewing the shape. This is a fixture choice,
not a modeling commitment; chunk 8 adds the modeled-resource form.

```click
resource shape(node: struct node*) {
    if node != 0 {
        owns node->left;
        owns node->right;
        contains shape(node->left);
        contains shape(node->right);
    }
}

contract void AugmentRotate(struct node* old, struct node* new) {
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= old->augmented;
    requires old->augmented < 1000;
    views shape(new);
    owns old->augmented;
    owns new->augmented;
    ensures 0 <= new->augmented;
    ensures new->augmented <= 1000;
}
```

The rotation helper's contract is modeled on `tree_rotate_left` in
`examples/binary-tree/binary_tree.click`: `requires node->right != 0;
consumes shape(node); produces shape(result); owns node->augmented;
owns node->right->augmented; requires AugmentRotate(augment_rotate)`. Its
proof unfolds `shape(node)` and `shape(node->right)`, steps the four
assignments, folds `shape(node)` then `shape(pivot)`, executes the callback
under the view, and returns. `bump` needs `requires 0 <= old->augmented;
requires old->augmented < 1000;` and `reset` needs no requirement; both
establish the two guarantees above.

**Expected verdicts.**

- `bump` and `reset` form `AugmentRotate(&bump)` and `AugmentRotate(&reset)`
  automatically at the call site (pass).
- `clobber` fails: its own contract must own `old->left`, which the named
  contract only views, so formation reports
  ``function `clobber` does not satisfy named contract `AugmentRotate` ``.
- `steal` fails: give it `consumes shape(old)` (ownership the named contract
  only lends); formation is rejected per
  `c_named_function_contract_rejects_ownership_from_view.md`.

**Files.** One positive mdtest `mdtests/augment_rotate_callback.md` with the
two passing callers, and two negative mdtests
`augment_rotate_callback_rejects_extra_write.md` and
`augment_rotate_callback_rejects_consumed_shape.md`. Each negative file must
contain the full C above (unchanged) and a caller that passes the bad
callback.

**Stretch, in the same chunk if cheap.** A realistic recompute reads the
children: `views old->left->augmented` guarded by `old->left != 0`. The
refinement obligation builder requires each clause to lower to exactly one
path (`let [path] = paths.as_slice()` in
`prepare_contract_refinement_obligations`); a guarded load may produce two.
If it does, record the exact clause that failed and stop; that is input to
chunk 7, not something to route around.

**Findings from chunk 3 (landed as `mdtests/augment_rotate_callback*.md`).**
The fixtures pass, but the helper contract had to take the root's two link
cells and the two subtree shapes instead of one folded `shape(node)`, because
of the first gap below. None of these is fixed yet; none has an issue file.

- A contract cannot own a memory segment whose base is loaded through a field
  that another owned or consumed composite in the same contract owns. Minimal
  repro: `resource pair(node: struct node*) { owns node->left; owns
  node->right; }` and a contract with `requires node->right != 0; owns
  pair(node); owns node->right->augmented;` fails certification. `views
  pair(node)` or owning the two links directly passes. Chunk 8a needs this
  fixed, since it wants `owns t: tree_at(new)` next to an augmentation
  footprint.
- That failure surfaces as `could not certify contract for 'probe':
  certification produced no paths`. The real error, a `CRuntimeError::
  FunctionContract("could not evaluate an owned memory resource segment")`
  from `evaluate_function_resource_context`, is discarded by
  `.ok().and_then(Result::ok)?` in `c_function_contract_certification_
  assumptions` (`src/kernel/api/contract_certification.rs`), and four other
  `?`s in that function drop errors the same way. This is a tooling defect
  under the "tooling stability comes first" rule and should be fixed before
  chunk 8: report the runtime error text, never an empty path set.
- A named contract whose resource clause reads through a parameter cannot be
  prepared: `requires old->left != 0; views old->left->augmented;` in
  `AugmentRotate` fails with `missing pure fact: loadable(base=old, bytes=8)`
  because the clause is lowered with no facts or resources in scope. This
  blocks the chunk 3 stretch item (guarded child reads) and any realistic
  recompute callback. It is earlier than the two-path limit the chunk
  predicted.
- Diagnostic wording: `src/surface/diagnostics.rs` renders an available
  `Contract(p)` fact on a symbolic pointer as ``named contract `X` is not
  established for p`` inside "available pure facts", which reads as the
  opposite of what it means.

## Chunk 4: explicit instance introduction in execution theorems

**Status: landed** as `d38cf746`. The rename of target clauses to the
introduced names is encoded as a field-free `ResourceField` substitution
entry guarded by instance identity (`resource_instance_rename_entry` in
`src/surface/lowering/contract_substitution.rs`); a dedicated substitution
variant would be cleaner if that map is touched again.

**Gap.** In `mdtests/c_contract_executes_counter.md` the proof writes
`step(Exact(cell))`, and in `c_contract_executes_counter_renamed.md` it
writes `step(Exact(counter))`. Neither `cell` nor `counter` is introduced by
the theorem; the checker makes the target contract's proof-parameter names
lexical inside the block. Replace that implicit rule with an `as` map on the
conclusion.

**Syntax.** When the target contract declares proof parameters, the
conclusion must carry a map from each target parameter name to a fresh name:

```click
theorem lift(callback: int32 (*)()) executes callback() {
    requires Exact(callback);
    ensures Progress(callback) as { counter: k } by {
        step(Exact(k));
        have k.revision == old(k.revision) + 1 by { assumption(); }
        apply(int32_increment_strictly_increases(old(k.revision), 2147483647));
        simp();
    }
}
```

Rules: every target proof parameter is named exactly once; an introduced name
must not collide with the callback, the call parameters, theorem lets, or
`result`; a target with no proof parameters takes no map, and an empty
`as {}` is accepted; a map on a target without proof parameters is an error.
The implicit rule is removed, not kept as a fallback, so there is exactly one
way names enter the block.

**Where.** Parser: the `executes` clause and `ensures` parsing in
`src/surface/parser.rs` (search for `"executes"` and for the comment
"Resource parameters of an executes target are lexical proof"). Checker:
`verify_execution_theorem` in
`src/surface/proof/pure_theorems/execution_theorems.rs`, where the target's
parameter names are currently bound. Printing and expansion must round-trip
the map (`src/surface/printing.rs`, `src/surface/expansion.rs`).

**Regressions.** Update all nine `c_contract_executes_counter*.md` fixtures
to the new spelling; they must keep their verdicts. Add:

- `c_contract_executes_as_missing.md` (fail): target has a proof parameter,
  no `as` map; the diagnostic names the missing parameter.
- `c_contract_executes_as_unknown_slot.md` (fail): the map names a parameter
  the target does not declare.
- `c_contract_executes_as_collision.md` (fail): the introduced name shadows a
  call parameter.
- `c_contract_executes_as_stale_name.md` (fail): the body uses the target's
  declared parameter name instead of the introduced one; expect an
  unknown-name diagnostic, proving the implicit rule is gone.

**Docs.** Rewrite the "resource proof parameters" paragraph under "Callback
execution theorems" in `docs/reference/language/index.md`.

## Chunk 5: binder transport at ordinary C call sites

**Gap.** A C function whose sidecar declares instance binders cannot be
called from C. `execute_verified_function_templates` in
`src/kernel/functions.rs` returns the runtime error "calls with named
resource instances require checked binder transport, which is not supported
yet" whenever any callee resource clause is a `CResourceSpec::Instance` and no
selected contract application is present.

**Syntax.** A call step names the callee and maps each of the callee's
binders to an owned instance of the caller:

```click
void increment(int32* state) {
    owns first: Counter();
    ensures first.revision == old(first.revision) + 1;
}

void twice(int32* state) {
    owns c: Counter();
    requires c.revision < 2147483646;
    ensures c.revision == old(c.revision) + 2;
} by {
    step(increment(state), { first: c });
    step(increment(state), { first: c });
    simp();
}
```

The first argument is the C call as written in the source, so `step` still
selects one call statement. The map is required whenever the callee has any
`owns`, `consumes`, or `produces` instance binder; a callee with none takes
no map. `owns` and `consumes` binders map to instances the caller owns;
`produces` binders are introduced by `let`:

```click
let root = step(tree_node_init(node, v, left, right), { l: a, r: b });
```

A `produces` binder that is not bound by `let` is an error, as is a map entry
for a binder the callee does not declare, a missing binder, a duplicate, or
an instance the caller does not own.

**Semantics.** Reuse the `ResourceCallApplication` path that
`step(Contract(instances))` already takes: build the binding from the map,
then run the same transition. `consumes` removes the instance; `owns`
returns the same identity with fresh post fields related only by the callee's
guarantees (see the "Returned ownership keeps its identity" comment in
`execute_verified_function_templates`); `produces` creates a fresh instance
under the `let` name. Unmentioned caller instances frame. No search: the map
is the only source of bindings.

**Where.** Parser and lowering of `step(...)` in `src/surface/parser.rs` and
`src/surface/proof/proof_object/execution_statements.rs` (search for
`selected_call_resource_arguments`); kernel in
`execute_c_function_contracts_paths` and
`execute_verified_function_templates`, `src/kernel/functions.rs`.

**Regressions.**

- `c_call_binder_transport.md` (pass): the `twice` example above.
- `c_call_binder_transport_produces.md` (pass): a caller that `let`-binds a
  produced tree instance and folds it into a parent, based on
  `resource_independent_children.md`.
- `c_call_binder_transport_frames_other.md` (pass): the caller owns a second
  instance that is not mapped and proves its fields unchanged.
- `c_call_binder_transport_rejects_missing.md` (fail): callee has a binder
  the map omits.
- `c_call_binder_transport_rejects_unowned.md` (fail): the mapped name is not
  an owned instance.
- `c_call_binder_transport_rejects_no_implicit_preservation.md` (fail): the
  caller claims an unmentioned field of the transported instance is
  unchanged; mirrors `contract_resource_call_no_implicit_preservation.md`.
- A scaling entry in `src/surface/tests/scaling_tests.rs` if the binding is
  anything other than a map lookup per entry.

**Docs.** A new subsection under "Read and write resources" in
`docs/reference/language/index.md` covering the call map and `let`.

## Chunk 6: concrete-callee execution theorems

Depends on chunks 4 and 5. This is the explicit route for proving that a
concrete function satisfies a named contract with proof parameters, which the
`unfold(Name)` route refuses.

**Syntax.** `executes` may name a verified C function instead of a callback
parameter. The theorem then has no callback parameter and no source-contract
premises; the source is the function's own verified contract:

```click
theorem increment_is_exact() executes increment(int32* state) {
    ensures Exact(&increment) as { cell: c } by {
        step(increment(state), { first: c });
        simp();
    }
}
```

The proof state starts from `Exact`'s requirements and resources with `c`
bound to an arbitrary `Counter()` instance, exactly as the abstract form
starts from its target. The single `step` runs `increment`'s verified
contract through the chunk 5 transport with `first` bound to `c`. The proof
must then establish `Exact`'s guarantees and return its resources.
`apply(increment_is_exact())` at a call site introduces `Exact(&increment)`
as today.

Restrictions for this slice: the callee must be a verified or explicitly
external function in the project; its parameter list in the `executes`
clause must match the C signature by type; exactly one call in every
feasible case, as for the abstract form; no extra theorem parameters.

**Where.** `verify_execution_theorem` in
`src/surface/proof/pure_theorems/execution_theorems.rs` dispatches on the
callback parameter; add the concrete case beside it. The kernel authority for
the resulting fact is the same shape as `prove_executed_contract_refinement`
in `src/kernel/api.rs`, with the concrete `PointerBlock::Function` target
instead of `FunctionSymbolic`.

**Regressions.**

- `c_contract_executes_concrete.md` (pass): the example above plus a caller
  that applies the theorem and passes `&increment`.
- `c_contract_executes_concrete_model.md` (pass): a modeled tree resource,
  a function with `owns t: tree_at(p); ensures t.model == old(t.model);` and
  a named contract with `owns root: tree_at(p)` promising the same; the
  theorem binds `{ root: r }` and `{ t: r }`.
- `c_contract_executes_concrete_rejects_weaker.md` (fail): the function
  promises less than the target.
- `c_contract_executes_concrete_rejects_unknown.md` (fail): `executes` names
  a function with no verified or external contract.
- `c_contract_executes_concrete_rejects_signature.md` (fail): the parameter
  list disagrees with the C signature.

**Docs.** Extend "Callback execution theorems" with the concrete form.

## Chunk 7: widen the refinement proposition filter

**Status: landed** as `7ff56487`, before chunk 6, so the printed theorem
skeleton does not yet parse until chunk 6 lands. Three caveats for later
chunks:

- Forced binding is keyed by resource family only: two binders of one family
  on either side refuse even when their arguments would disambiguate. That is
  stricter than the name-plus-arguments rule above and is fine until a
  fixture needs otherwise.
- Post instance fields are always fresh, including for a binder the
  implementation returns unchanged, matching the ordinary call rule; a
  contract promising field preservation is refined only by an implementation
  that states it.
- The skeleton spells an aggregate-pointer parameter by its pointer type,
  since the kernel interface keeps a layout, not a struct tag. Chunk 8's
  rbtree fixtures will print `struct node*` imprecisely; fix the spelling
  there if the fixture asserts it.
- `CResourceSpec::Instance` now carries `binder: String`; chunk 5 should
  reuse it for its call map rather than add a second spelling field.

Independent of chunks 4 through 6 in code, but write its fixtures after
chunk 6 so the explicit route exists for the failing cases.

**Gap.** `spec_expression_supports_stateful_memory_refinement` in
`src/kernel/functions.rs` returns false for `SpecExpression::ResourceField`,
`AlgebraicMatch`, and `SpecPureFunctionArgument::Algebraic`, so a clause such
as `ensures root.model == old(root.model)` cannot participate in refinement
even when both sides bind the same instance. The obligation lowering already
evaluates `ResourceField` through `resource_instance_at_path` (see
`src/kernel/spec.rs`); only the filter and the entry/post instance plumbing
block it.

**Scope.** Admit resource fields on current and entry memory, algebraic
equality, `AlgebraicMatch`, and algebraic pure-function arguments. Keep
`at(...)`, explicit memory snapshots, `CountedResourceCount`, and `RangeFold`
excluded; those need an explicit theorem and the exclusion stays documented.
Read the `SpecProposition` and `SpecExpression` enums in
`src/kernel/primitives.rs` and enumerate every variant explicitly; no
wildcard `true`.

**Automatic formation.** With proof-parameter contracts, passing `&f` with no
theorem may form the fact only when the binding is forced: for each target
proof parameter there is exactly one implementation binder with the same
resource name and equal evaluated arguments, and vice versa. Otherwise fail
with a diagnostic that names the ambiguity and points at the chunk 6 theorem
form. No search, no ranking, no fallback across candidates.

The automatic route stays exact-only: `contract_refinement_proves` in
`src/kernel/functions.rs` is an exact assumption lookup or the frozen
condition decider on a bare condition, and its cost is linear in the two
contracts plus the caller memory havoc. Do not add logical descent, rewrite
search, or case enumeration to it; those belong in the explicit theorem. Do
not add a memo unless a scaling regression shows repeated formation at many
call sites; if one is added, key it by the contract and function names, never
by structural comparison.

**Failure diagnostic.** When automatic formation refuses a concrete target,
print the explicit theorem skeleton the user needs, with the slots filled
from the two contracts:

```
function `bump` does not satisfy named contract `AugmentRotate` automatically;
prove it explicitly:
theorem bump_is_augment_rotate() executes bump(struct node* old, struct node* new) {
    ensures AugmentRotate(&bump) as { t: r } by {
        step(bump(old, new), { tree: r });
        simp();
    }
}
```

For a target without proof parameters emit the `unfold(Name)` form instead.
This is the expand affordance for the automatic route; it must be produced
from the same interfaces the check used, so the two routes cannot disagree
about the obligation. Add `c_named_contract_refusal_prints_theorem.md`
(fail) asserting the skeleton text.

**Regressions.**

- `c_named_contract_refines_model_automatic.md` (pass): one binder on each
  side, the fact forms at the call site with no theorem.
- `c_named_contract_rejects_weaker_model_guarantee.md` (fail): the
  implementation promises only `t.model != HeapTree::Empty`.
- `c_named_contract_rejects_ambiguous_binding.md` (fail): two binders of the
  same resource on one side; the diagnostic names both and the theorem form.
- `c_named_contract_rejects_unmatched_binder.md` (fail): the implementation
  requires an instance the named contract does not supply.
- A scaling entry in `src/surface/tests/scaling_tests.rs` if the
  forced-binding check is anything other than a map lookup per binder.

**Docs.** Update the "What refinement admits" sentence wherever it appears in
`docs/reference/language/index.md` and `docs/concepts/contracts.md`.

## Chunk 8: the rbtree-shaped regressions

Depends on chunks 1 through 7. These are the two regressions in the
acceptance criteria, now written against Linux's signatures.

**8a. Model-preserving rotation.** Reuse the chunk 3 C source verbatim. Add a
sidecar that models the tree with an algebraic `HeapTree`-style resource (see
`examples/modeled-binary-tree/modeled_binary_tree.click`) that owns links and
the augmentation cell together, and a proof-parameter contract
`contract AugmentRotate(t: tree_at(new)) for void(struct node* old,
struct node* new) { owns t; ensures t.model == old(t.model); ... }` plus a
footprint on the two augmentation cells. `bump` and `reset` pass through
chunk 6 theorems or chunk 7 automatic formation; `clobber` fails on the
model guarantee, not just on footprint; `steal` fails as before.

**8b. Three-callback table.** C source mirroring `rbtree_augmented.h` without
the parent-color word:

```c
struct rb_augment_callbacks {
    void (*propagate)(struct node *node, struct node *stop);
    void (*copy)(struct node *old, struct node *new);
    void (*rotate)(struct node *old, struct node *new);
};
```

with `dummy_propagate`, `dummy_copy`, `dummy_rotate` bodies as in
`lib/rbtree.c` (each a no-op), a `static const struct rb_augment_callbacks
dummy_callbacks = { ... }` table, an erase-shaped helper taking
`const struct rb_augment_callbacks *augment` that calls all three, and a
caller passing `&dummy_callbacks`. The sidecar gives each field a distinct
named contract (`Propagate`, `Copy`, `Rotate`) carried as facts in a
`callback_suite`-style resource over the table, as in the pipeline mdtest, and
the helper `views` that resource. Two fixtures: the caller with the const
table (concrete formation of each field), and the helper verified alone (three
abstract facts, distinct contracts, no enumeration). A negative fixture binds
`.rotate` to a function that satisfies `Copy` but not `Rotate`.

**8c. Inline entry points.** Note in the fixture prose, not in code, that
inside `lib/rbtree.c` the always-inline `__rb_insert` binds its callback
concretely at each call site and needs no contract; only the exported
non-inline entry points need `AugmentRotate(augment_rotate)`. Verification of
the pinned upstream source itself belongs to
`issues/linux-rbtree-inline-helpers.md` and
`issues/kernel-scale-preprocessing.md`.

## Chunk 9: close-out

- Rewrite the callback paragraphs in `docs/reference/language/index.md`
  ("Pure theorems", "Callback execution theorems") and
  `docs/concepts/contracts.md` so the naming rule above, the admitted
  proposition and resource classes, and the exclusions from chunk 7 are each
  stated once.
- Update `docs/reference/language/limitations.md` for bare designators and
  const callback tables.
- Delete this file and its line in `issues/README.md` once every chunk's
  fixtures and `scripts/check.sh` are green.

## Acceptance criteria

- A bare function designator forms the same address as `&name` in every
  value position (chunk 1).
- File-scope and static const struct objects may have function-pointer fields
  initialized with function addresses; loads through them dispatch exactly
  (chunk 2).
- An unchanged rotation helper with a callback over two struct pointers
  verifies against a callback contract that views the tree shape and owns
  only the augmentation cells; two conforming callbacks pass and a callback
  with an extra write or a consumed resource fails at formation (chunk 3).
- Execution theorems introduce every name explicitly; the implicit
  target-parameter scoping is gone (chunk 4).
- A C function with instance binders can be called with an explicit binder
  map, and produced instances are `let`-bound (chunk 5).
- A concrete function's refinement of a proof-parameter contract is a
  checked `executes` theorem in the same spelling as the abstract form
  (chunk 6).
- Named-contract refinement admits resource fields and algebraic values,
  forms automatically only under a forced binding, and has a documented,
  regression-covered exclusion list (chunk 7).
- The model-preserving rotation and the three-callback const table verify,
  with the stated negative fixtures failing (chunk 8).
- `scripts/check.sh` passes.

Related: [struct-model.md](struct-model.md),
[global-variables.md](global-variables.md),
[linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md).
