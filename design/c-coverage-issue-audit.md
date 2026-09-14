# C coverage issue audit, 2026-09-14

Audited base: `d9b4daa16bdb25727b34b36301be3cfda3c3fe35`.
Scope: the P1 `multi-function-files-and-headers` and `struct-model` issues,
including their acceptance criteria, implementation, executable regressions,
documentation, and ownership of remaining work. This is a completion audit,
not an exhaustive soundness review of the C frontend or resource kernel.

## Decision

Close both umbrella issues and remove their P1 entries. Neither needs a new
replacement issue or a blanket P2 entry. Their concrete supported-subset
milestones are implemented. The remaining full-C aspirations are documented
subset boundaries or already belong to other issues. Keeping the umbrellas
open makes delivered functionality look like pending launch work.

The original issue histories and numbered milestones remain in Git. The
[Supported C0 reference](../docs/reference/language/c0.md) and
[limitations](../docs/reference/language/limitations.md) are the lasting
user-facing descriptions. No C, verifier, resource, or loan implementation is
changed by this audit.

## Multi-function files and headers

The opening diagnosis describes the 2026-09-01 parser, not the current code.
The concrete acceptance criteria are covered by the following:

| Requirement | Current evidence |
| --- | --- |
| Multiple definitions, forward prototypes, contracts by C name | `mdtests/multiple_functions_per_source.md`; `c0_parses_multiple_definitions_and_forward_prototypes` and `c0_rejects_conflicting_function_prototypes` in `src/languages/c/tests.rs` |
| Shared declarations across translation units, nested relative includes | `mdtests/local_headers.md`; `include_expansion_collects_transitive_headers` and `local_include_paths_resolve_relative_to_including_file` in `src/languages/c/source.rs` |
| Header guards and pragma once | `mdtests/header_guards.md`, `pragma_once_header.md`, `header_guard_rejects_mismatch.md`; diamond expansion and guard-undefinition unit regressions |
| Inline bodies, allowed attributes, linkage and source diagnostics | `mdtests/inline_functions_in_headers.md`, `always_inline_functions_in_headers.md`, `always_inline_attributes_in_headers.md`, `inline_helper_sidecar.md`, `inline_header_error_location.md`, `conflicting_inline_helpers_across_headers.md`, `duplicate_inline_helpers_across_headers.md`, `local_header_rejects_function_definition.md` |
| Modeled standard headers and unknown-header rejection | `mdtests/system_stdint_header.md`, `system_header_rejects_unknown.md`; current `source.rs` allowlist additionally includes `inttypes.h` and `stdbool.h` |
| Object macro expressions, strings, aliases, continuations and bounds | `mdtests/object_like_macros.md`, `object_like_macro_expression.md`, `object_macro_version_header.md`; `object_macros_expand_expressions_strings_aliases_and_comments`, `object_macro_recursion_and_amplification_are_bounded`, token-boundary and redefinition tests in `source.rs` |
| One-to-three-parameter substitution, nested arguments and rejection boundary | `mdtests/function_like_macros.md`, `multi_parameter_function_macros.md`, and the `function_like_macro*rejects*` fixtures; arity, recursion and replacement tests in `source.rs` |
| Conditional compilation, macro-state changes, inactive branches and diagnostics | `mdtests/conditional_compilation.md`, `conditional_compilation_rejects_expression.md`, `undefined_preprocessor_identifiers.md`; boolean/equality/elif/defined/undef and malformed-structure tests in `source.rs` |
| Missing includes and cycles | `include_expansion_reports_missing_headers_and_cycles` in `src/languages/c/source.rs` |

`expand_includes`, the source directive/macro implementation, and the C parser's
header/declaration validation are the implementation boundaries inspected.
Macro recursion and amplification have explicit depth, output-byte, and work
bounds. The source expander remains a bounded subset, not a general C
preprocessor.

The issue's request to replace repeated declarations in examples describes the
capability motivation. `local_headers.md` proves that sharing works across
unchanged fixture translation units. The frozen synthetic `jsonc-refcount`
example still repeats its declaration; rewriting that C is unnecessary for
closure and would not establish any new verifier capability.

The old issue's statements that only `stdint.h` is supported and that object
macros are literal-only were superseded by the implementation. They are not
reasons to restore rejection of already supported forms.

## Struct model

All 24 numbered milestones are marked delivered, and all 32 distinct mdtest
paths cited by the issue exist with `expect pass`. The ordinary mdtest harness
has no quarantined entries. The grouped evidence below covers the original
numbered milestones and acceptance criteria:

| Milestones / requirement | Representative executable evidence |
| --- | --- |
| 1–3: byte arrays, embedded structs, array indexing and named enums | `struct_inline_byte_array`, `struct_embedded_scalar_field`, `local_array_of_structs`, `struct_array_parameter_fields`, `struct_enum_field` |
| 4, 7–9: scalar, nested, pointer and embedded-array by-value copies | `struct_by_value_scalar_copy`, `struct_by_value_enum_copy`, `struct_by_value_array_copy`, `struct_by_value_embedded_copy`, `struct_by_value_pointer_copy`, `struct_by_value_embedded_array_copy`, `struct_by_value_embedded_array_multidim_copy` |
| 5, 23–24: tagged-union reads, addresses and overlapping copies | `struct_tagged_union`, `struct_union_member_address`, `struct_union_by_value_copy`; negative `struct_tagged_union_rejects_writes` |
| 6, 11: multidimensional array shape and stride | `struct_array_of_embedded_structs`, `struct_multidimensional_embedded_array`, `struct_multidimensional_scalar_array` |
| 10, 12–13: field addresses, scalar width and layout | `struct_field_address`, `struct_scalar_array_element_address`, `struct_wide_scalar_fields`; negative `struct_byte_array_resource_range_rejects_neighbor` |
| 14–16: aggregate clauses, lvalue copies, helper views and return relations | `struct_aggregate_resources`, `struct_aggregate_load_copy`, `struct_aggregate_helper_view`, `struct_aggregate_return_postcondition` |
| 17–21: local initialization, conditionals and designators | `struct_aggregate_initializer`, `struct_conditional_value`, `struct_designated_initializer`, `local_struct_array_initializer`, `local_struct_array_designators` |
| 22: callback field signatures, loads and direct calls | `struct_function_pointer_field`, `struct_function_pointer_field_direct_call`; wrong-signature/nominal-argument unit regressions |
| By-value boundary and initialization rejection | `by_value_struct_param_ensures_rejected`, `by_value_struct_param_old_ensures`, `aggregate_copy_uninitialized_source_rejected`, `aggregate_copy_skipped_field_rejected`, `aggregate_return_uninitialized_source_rejected` |

Names in the second table denote files under `mdtests/` with the `.md` suffix.
The C unit tests additionally check nested/row-major layout, typed lowering,
copy execution, callback metadata, and union overlap. In particular,
`c0_lp64_layout_matches_the_host_c_abi` checks field offsets, alignment and size
against a Rust `repr(C)` record on an LP64 host. This is evidence for the
current profile, not a cross-compiler or cross-architecture guarantee.

Inspection of `scalar_struct_value_layout` and aggregate/callback lowering in
`src/languages/c/syntax.rs` confirms support has overtaken several old issue
paragraphs: callback fields are copyable, named-contract field calls exist,
and supported union-containing structs retain overlapping member views during
copies. Static designated aggregate initialization also has its own passing
fixtures. The audit corrects contradictory reference/limitations prose rather
than treating stale rejection criteria as new implementation tasks.

## Boundaries and existing owners

| Remaining concern | Disposition |
| --- | --- |
| Full configured Linux preprocessing and retained GNU/header forms | Keep with `issues/kernel-scale-preprocessing.md` and `issues/linux-rbtree-inline-helpers.md`, under their existing priority and approved scope. Closing the bounded importer issue does not prove the pinned Linux translation unit works. |
| Other compiler profiles, packing, bitfields and ABI-dependent layout | Already owned by `issues/multiple-compilers.md` (P2). |
| Static aggregate initialization extensions, static object contracts and callback-table resource packaging | Already owned by `issues/global-variables.md` and the specific static-state/resource issues. Do not duplicate them under structs. |
| Borrow stability, resource transport and abstract callback ownership | Remain with `issues/fix-views.md`, `issues/memory-vs-resources.md`, and their active work. Aggregate-shape coverage does not certify the candidate stable-view implementation. |
| General union writes, standalone union values and broader initializer shapes | Retain the explicit unsupported-subset documentation. The audited issues supply no independent failing launch regression requiring a new issue. |
| Complete rbtree algorithm proofs | Still owned by `issues/rbtree-example.md`. The frontend milestones do not establish its functional correctness or termination. |

The examples gate currently quarantines `multifile-registry` for the separately
tracked static-state caller-transport problem. That is not a parser/header
coverage failure. No quarantine or issue priority outside these two umbrellas
is changed by this audit.

## Validation

The focused C parser/source unit run passed all 313 selected tests (exit 0):
`RUST_MIN_STACK=8388608 cargo nextest run --lib -E
'test(languages::c::source::tests::) | test(languages::c::tests::)'`.

The full unpiped `scripts/check.sh` passed (exit 0), including formatting,
lints, documentation, unit tests, and the ordinary mdtest, example and
compiler-import gates. All 32 fixtures cited by the struct issue passed in
that unfiltered run. The verdict comes from command exit status,
not filtered log text. The ordinary resource interpretation is used; this audit
does not run or certify the ongoing candidate stable-loan migration.
