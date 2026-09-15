# Extend static-storage initializers and string-literal coverage

**Priority: P2. Audited 2026-09-14 at `c3283eb2`.** The original P1
file-scope objects, statics, and basic string-literal milestone is delivered.
This issue retains broader initializer/literal coverage; it no longer stands
for implementing global storage from scratch. The remaining const callback
suite integration is P1 under [rbtree C6](rbtree-example.md),
and [stable views](../docs/internals/stable-views.md); the resource and
callback transport it also waited on landed on 2026-09-15.
It is not closed by this audit or demoted with the language-coverage remainder.

## Delivered scope

The original audit was at `cb034b21` on 2026-09-01. Current code and tests have
substantially overtaken that diagnosis:

| Delivered capability | Representative evidence in `mdtests/` |
| --- | --- |
| Stable scalar globals, cross-file extern linkage, private statics and ordinary current-value contracts | `file_scope_globals.md`, `file_scope_static_globals.md`, `global_entry_requires_current_value.md`, `file_scope_global_link_errors.md`, `file_scope_static_link_errors.md` |
| Data-only translation units, typed objects and relocations | `data_only_translation_unit.md`, `data_only_duplicate_definition.md`, `data_only_private_not_external.md` |
| Tentative-definition coalescing, incomplete extern arrays and compatible shape resolution | `file_scope_tentative_globals.md`, `file_scope_tentative_arrays.md`, `file_scope_tentative_aggregates.md`, `file_scope_incomplete_extern_arrays.md`, and their link-error regressions |
| Fixed/inferred scalar arrays, supported multidimensional shapes and one-dimensional struct arrays | `file_scope_multidimensional_arrays.md`, `file_scope_inferred_multidimensional_array_bounds.md`, `file_scope_static_inferred_multidimensional_array_bounds.md`, `static_array_parity_aggregate.md`, `static_array_parity_scalar.md`, `static_array_parity_multidimensional.md`, `static_array_parity_fixed_multidimensional.md` |
| Constant-expression initialization, selected conditional branches, casts and supported designators | `static_integer_constant_initializers.md`, `static_integer_constant_expression_control.md`, `designated_aggregate_static_objects.md`; parser tests cover sparse scalar designators independently of the outstanding caller fixture below |
| Const storage and callback-table dispatch/refinement | `const_global_table.md`, `const_aggregate_objects.md`, `const_callback_table_dispatch.md`, `const_callback_table_abstract.md`, and their write/signature rejection fixtures |
| Function-local static storage and ownership transfer without initializer reset | `static_scalar_locals.md`, `static_local_arrays.md`, `program_entry_static_ownership.md`, `private_state_mutation_reset.md`, `private_state_wide_return.md` |
| Resources over globals and private objects from several files | `qualified_static_resource.md`, `qualified_static_ownership.md`, `qualified_static_struct.md`, `qualified_function_static_ownership.md` |
| Stable object/subobject address initializers | `static_subobject_pointer_initializers_cross_file.md`, `static_initializer_dependency_chain_cross_file.md`, `static_pointer_initializer_const_discard.md`; the general pointer-initializer caller below remains incomplete |
| Basic ASCII strings, supported escapes, adjacent-literal concatenation, read-only storage and call propagation | `string_literals.md`, `string_literals_call.md`, `string_literals_reject_write.md`, `concatenated_string_literals.md`, `concatenated_string_literals_rejected.md` |

Implementation evidence includes the declaration/linking/constant-initializer
and string-literal tests in `src/languages/c/tests.rs`, static initialization
in `src/kernel/functions.rs`, and
`src/kernel/functions/program_entry_tests.rs`.

The old acceptance requirement to materialize initializer values at every
function entry was incorrect. Static storage is initialized once at program
startup. A parameterless `main` proof receives initialized writable ownership
and const views; ordinary function entry neither restores mutable initializers
nor mints fresh ownership. Ordinary contracts describe current state and use
`old(...)` for their entry snapshot. `global_entry_initializer_rejected.md`,
`static_entry_initializer_rejected.md`, and the kernel startup/call tests
protect this boundary. Do not restore the old behavior to make a caller pass.

The retired `global_effect_requires_mutable.md` reference is superseded by
`global_write_requires_ownership.md` and the field/array effect regressions.
Automatic local aggregate designators and adjacent basic string concatenation
are also implemented, despite the old issue's final unsupported list.

## Remaining P1 integration: const callback suites

The blanket statement that resources over globals are inexpressible is false:
`qualified_static_resource.md` folds and passes a resource containing private
mutable globals from two translation units, starting at `main`.

For const callback tables the distinction is read authority versus ownership.
The unchanged C in `rb_augment_callbacks_table.md` already verifies using
explicit named contracts on the table fields. A combined packaged caller and
helper now verifies as
`rb_augment_callbacks_const_suite.md`:

- `callback_suite` contains `views` of its three const callback cells, not
  `owns` of those cells;
- explicit refinement theorems establish the three concrete contract facts
  before folding; and
- caller and helper state matching field-level separation from the callback
  node. This is conditional local verification under those premises, not a
  derivation of separation for arbitrary external pointers.

The same fixture now passes under the shipped stable-view semantics; the
candidate-mode refusal it once hit (`an exclusive instance inside a composite
view is unsupported`) was resolved before the cutover recorded in
[the stable views record](../docs/internals/stable-views.md). Preserve the
unchanged C, required callback guarantees and read-only table storage. Do not
mint write authority for const cells, make the table writable, or require an
artificial `main` in a library proof merely to manufacture the package. The
final proof must also handle real mutation-capable augmentation callbacks and
their effects, which is rbtree C6 work; the no-op audit fixture does not
complete that requirement.

`object(&static_object)` still fails parsing with
`object(...) currently expects a named C struct pointer parameter`. The parser
in `src/surface/parser.rs::parse_current_contract_segments_inner` requires a
named struct-pointer parameter. Field ranges can express the relevant table
separation, as the ordinary passing suite shows. Generalizing the convenience
spelling is therefore deferred unless an unchanged MVR proof exposes an
obligation that cannot be expressed with the existing field ranges. No
unconditional separation between a static object and an arbitrary external
argument may be assumed.

## Existing P2 caller and linkage work stays separate

Five fixtures cited as delivered coverage in the old issue currently expect
`fail: run.contract`, not success. They must not be counted as positive
end-to-end evidence. Audit verification reproduced their current failures:

| Fixture | Current failure |
| --- | --- |
| `aggregate_static_objects.md` | A post-call equality needed by `have` is not derived. |
| `initialized_aggregate_static_objects.md` | A post-call equality needed by `have` is not derived. |
| `designated_scalar_static_arrays.md` | The next `read_private` precondition is not established. |
| `initialized_aggregate_static_arrays.md` | Owned entry clauses cannot be evaluated in a dependency order. |
| `static_pointer_initializers_cross_file.md` | The final sum reports possible signed overflow. |

These observations do not prove one common verifier defect: contract permission
coverage, proof steps, dependent resource evaluation and state transport must
be distinguished. The related work belongs with
[static-state-caller-transport.md](static-state-caller-transport.md), and any
resource-engine defects with their existing owners. That issue also retains
`examples/multifile-registry`, which remains quarantined in the ordinary gate.
Their initializer syntax and layout can have parser coverage while their caller
proofs remain incomplete. No expectation or quarantine is changed by this audit.

[linked-initializer-private-names.md](linked-initializer-private-names.md)
retains the defining-translation-unit initializer-resolution gap.
[private-static-helper-ownership.md](private-static-helper-ownership.md)
retains the unchanged upstream PCG wrapper/client acceptance work. Neither is
an additional global-storage implementation milestone or a demonstrated
rbtree dependency.

## Deferred language coverage

Retain these original broader requirements as P2, without requiring them to
close the P1 rbtree/static-table work:

- Inferred bounds with element designators, including
  `int table[] = { [2] = 7 };` and the corresponding supported struct-array
  forms. The bound must follow the selected elements and omitted cells remain
  zero-filled.
- Multidimensional static arrays of structs, broader nested/designated
  initializer shapes, and remaining valid incomplete/tentative-definition
  completion rules. Preserve shape, linkage identity, ABI stride and one-time
  initialization; unresolved extern declarations must still be rejected.
- Additional legal integer constant-expression forms in designators and
  initializers. Calls or runtime loads in C static initializers remain invalid;
  this issue does not authorize accepting them or adding C++ dynamic startup.
- Wider literal prefixes/encodings, non-ASCII characters and additional escape
  forms, with explicit element types and encoding semantics. Basic ASCII and
  adjacent basic literals are already delivered.
- General `object(...)` syntax for static aggregate addresses, if useful after
  the current field-based specification path; it must preserve exact object
  identity and layout and confer no new permissions.

## Acceptance criteria for the retained P2 work

Use small unchanged C fixtures for each chosen extension. Verify initial values
at actual startup (for example, a supported `main` returning `table[2]`), or
state current-value preconditions at ordinary entry; then cover retained state
across calls. Preserve duplicate-definition, incompatible-shape, unknown-name,
const-write, ownership and stale-initializer rejection tests. Keep syntax-only
coverage distinct from passing program proofs and from known negative caller
fixtures. Run focused tests and the full unpiped `scripts/check.sh`; update
[Supported C0](../docs/reference/language/c0.md) as each supported boundary grows.

The original completion history remains in Git.

## Audit validation

Of the 54 explicit fixture paths in the old issue, 53 still exist: 27 expect
success and 26 expect rejection. The missing path has the ownership-based
replacement noted above. The five incomplete caller fixtures were reproduced
without changing their expectations. The focused callback fixture gate passes,
and `click audit mdtests/rb_augment_callbacks_const_suite.md` checks all 16 smart
tactic sites across eight claims successfully. The full unpiped
`scripts/check.sh` exits successfully, including the new fixture.
