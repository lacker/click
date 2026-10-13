# Language coverage

This page states, for each program language Click verifies, which source
features and runtime errors a proof covers. Use it to decide whether Click
applies to a codebase before reading the per-language references:
[supported C](language/c.md), [C++ import](cli/import.md#preliminary-c-semantic-artifact),
and [Rust import](rust.md). Those pages define the exact forms; this page is
the single summary, and other pages link here instead of repeating it.

C, C++, and Rust share one proof language, one execution and memory model, and
one kernel. Coverage differs only in which source constructs each frontend
admits. Anything outside the admitted subset is refused with a diagnostic; it
is never silently approximated.

## How to read the matrix

Each cell has one status:

- **Supported**: the construct is admitted as written, and the cited fixture
  verifies it or, in the runtime-error tables, shows the error being refused.
- **Partial**: a documented subset is admitted. The qualifier names the main
  boundary; the linked reference has the complete boundary.
- **Not supported**: source using the construct is refused at import or
  verification.
- **Not applicable**: the construct or error cannot arise in the admitted
  subset, for the stated reason.

Every Supported or Partial cell cites one fixture: an mdtest under `mdtests/`,
an example or integration directory, or a Rust test written as
`FILE::TEST_NAME`. A documentation test checks that each cited fixture exists.

All three languages are checked against one machine: x86-64 Linux, LP64,
little-endian, eight-bit bytes. A proof says nothing about other targets.

## How source gets in

The frontend that reads source is trusted for its semantics: Click's own
parser for C (with the GCC preprocessor in import mode), Clang's typed AST
and Click's exporter for C++, and rustc's type and borrow checking plus
Charon's ULLBC for Rust. Each import records its toolchain in a lock, and
verification then runs offline.

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Verify without a compiler | Supported: Click parses C directly; `mdtests/local_array.md` | Not supported: needs the pinned Clang exporter at lock time | Not supported: needs pinned Charon at lock time |
| Compiler-backed import, verified offline | Partial: GCC preprocessing only, fixed flag profiles, with Click's modeled system headers; `tests/compiler_import.rs::compiler_import_supplies_clicks_modeled_headers_beside_project_flags` | Partial: one C++20 translation unit, one selected function and its reachable graph, Clang 19.1.7; `examples/basic-cpp/` | Partial: one file, or an explicit crate module closure without dependencies; `examples/basic-rust/` |
| Multiple files and modules | Supported: bundles of translation units and local headers; `examples/multifile-registry/` | Partial: definitions from one logical source; `tests/cpp_import.rs::included_header_definition_is_selected_locked_and_validated` | Partial: locked crate module closure, no third-party crates; `tests/rust_import/crate_inputs.rs::rust_crate_locks_all_compiler_inputs_and_preserves_qualified_calls` |

## Target and ABI

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| x86-64 Linux LP64 | Supported: `x86_64-linux-userspace` (default) and `x86_64-linux-kernel`; `mdtests/userspace_target_directive.md` | Partial: `x86_64-unknown-linux-gnu`, C++20, fixed exception and RTTI profile; `examples/basic-cpp/` | Partial: `x86_64-unknown-linux-gnu`, overflow checks on, `panic=abort`; `examples/basic-rust/` |
| Other targets (32-bit, big-endian, other OS or ABI) | Not supported | Not supported | Not supported |
| Kernel and user-space profiles | Supported: distinct predefines, headers, and artifact identity; `tests/compiler_import.rs::userspace_and_kernel_imports_have_distinct_identity_for_identical_c` | Not supported: hosted target only | Not supported: hosted target only; no `no_std` profile |
| Plain `char` signedness | Supported: signed under `x86_64-linux-userspace`, unsigned under `x86_64-linux-kernel`; `mdtests/userspace_plain_char_is_signed.md` | Not supported: plain and signed `char` are refused; `unsigned char` and `std::byte` only | Not applicable: bytes are `u8`; the `char` type is not admitted |
| Struct layout source | Partial: Click's own LP64 rules, not checked against a compiler; `mdtests/gnu_aligned_struct_layout.md` | Supported: Clang-reported layouts, checked; `tests/cpp_import.rs::distinct_record_layouts_keep_field_widths_offsets_and_ownership` | Supported: rustc-reported layouts; `examples/rust-move-drop/` |
| Packed structs, bit-fields | Not supported | Not supported | Not applicable: no `repr(packed)` admitted |

> **Note:** Plain `char` follows the selected C target: signed under
> `x86_64-linux-userspace`, as GCC and Clang build x86-64 user space by
> default, and unsigned under `x86_64-linux-kernel`, matching the kernel's
> `-funsigned-char`. As in GCC and Clang, where it is only a `-Wpointer-sign`
> warning, an uncast conversion between `char *`, `signed char *`, and
> `unsigned char *` is accepted and reads the bytes as the explicit cast
> would; `mdtests/a_uint8_pointer_passed_as_a_char_pointer_reads_signed_bytes.md`.

## Scalar types

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Integer widths | Partial: signed and unsigned 8, 16, 32, 64 bits; `mdtests/int64_uint64_arithmetic.md`, `mdtests/an_out_of_range_integer_constant_converts_modulo_its_destination_width.md` | Partial: signed and unsigned 32, 64, and limited 128 bits, plus `unsigned char`; `tests/cpp_import.rs::signed_scalar_arithmetic_verifies_through_the_shared_kernel_and_modular_calls` | Partial: `i32`, `u8`, `u16`, `u32`, `usize` only; `examples/rust-unsigned/` |
| Booleans | Supported: `_Bool` and `bool`; `mdtests/c_bool_parameter_range.md` | Supported: `tests/cpp_import.rs::locked_cpp_branch_and_early_return_verify_through_the_shared_sidecar_path` | Supported: `tests/rust_import.rs::rust_boolean_return_and_local_initialization_verify` |
| Integer casts | Supported: GCC's modulo 2^N conversion among 8, 16, 32, 64 bits, implicit or written, owing no range; `mdtests/int8_conversion_wraps_modulo_256.md` | Partial: C++20 conversions among admitted widths; `tests/cpp_import.rs::cpp20_unsigned_to_signed64_preserves_all_bits_at_boundaries` | Partial: `as` among admitted widths and core `From`; `examples/rust-integer-conversions/` |
| Floating point | Partial: IEEE binary32 and binary64, round-to-nearest-even only; no `long double` values, `fenv`, or bit casts; `mdtests/float_cancellation_is_exact.md` | Not supported | Not supported |
| Enumerations | Partial: named enum fields and constants; no enum parameters, returns, or locals; `mdtests/struct_enum_field.md` | Partial: scoped enums with `unsigned char` backing, including `std::byte`; `tests/cpp_import.rs::cpp_fixed_byte_enum_forwarding_verifies_and_retains_nominal_identity_offline` | Not supported: user enums and `match`; only the compiler's `Option` inside admitted iterator loops |

## Memory, pointers, and aggregates

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Pointers and references | Partial: typed data pointers of every scalar width, `T**`, struct pointers; `void *` is opaque only; `mdtests/c_void_pointers.md` | Partial: `int*`, `unsigned int*`, `unsigned char*`, `std::byte*`, `int&`, record references; no multilevel pointers; `examples/basic-cpp/` | Partial: `&T` and `&mut T` to scalars and structs; no reference returns or raw pointers; `examples/basic-rust/` |
| Pointer arithmetic | Supported: scaled, bounded by the object or held range; `mdtests/pointer_arithmetic_on_objects.md` | Partial: indexed offsets on admitted pointers; no pointer differences; `tests/cpp_import.rs::cpp_native_pointer_offsets_preserve_index_width_and_range_authority` | Not applicable: no raw pointers in safe Rust |
| Arrays and slices | Partial: fixed and multidimensional arrays in every storage class; no variable-length arrays; `mdtests/local_array.md` | Partial: `std::span<int>` through catalog contracts; no built-in array locals; `tests/bitcoin_core_money_range.rs::axiomatic_span_pop_back_verifies_against_catalog_contracts` | Partial: `&[u8]`, `&mut [u8]`, fixed `u8`/`u32`/`i32` arrays; no by-value array parameters; `examples/rust-slices/` |
| Structs and records | Partial: scalar, pointer, array, embedded, and function-pointer fields; by-value copies; `mdtests/struct_wide_integer_arrays.md` | Partial: trivially copyable records, single non-virtual base chains; `tests/fixtures/cpp-verification/class-record/` | Partial: flat structs and tuple structs, moves and `Drop`; no nested owned fields; `examples/rust-move-drop/` |
| Unions | Partial: named unions read through members; no member writes or union values; `mdtests/a_branch_join_keeps_a_union_view_neither_arm_writes.md` | Not supported | Not supported |
| Globals and statics | Supported: scalar, array, and aggregate objects with program-entry ownership; `mdtests/file_scope_global_arrays.md` | Partial: `constexpr` constants only; mutable globals refused; `tests/fixtures/cpp-verification/constexpr-coin/` | Partial: local scalar `const` items; no `static`; `tests/rust_import/crate_inputs.rs::rust_crate_scalar_constants_execute_checked_initializers` |
| Heap allocation and free | Partial: modeled `malloc`, `calloc`, `realloc`, `free` forms; no zero-size or custom allocators without contracts; `examples/heap-object/` | Not supported: no `new`, `delete`, or owning containers | Not supported: no `Box`, `Vec`, or other heap owners |
| Object lifetimes and destructors | Supported: automatic storage, block exit, `free`; `mdtests/freed_pointer_set_to_null_verifies.md` | Partial: up to two `noexcept` destructible locals per cleanup scope; `tests/cpp_import.rs::two_constructed_objects_are_destroyed_in_reverse_order_on_every_return` | Supported: compiler-selected drop order and drop flags; `tests/rust_import.rs::rust_two_guards_clean_up_in_reverse_construction_order` |

## Control flow and functions

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Branches and early return | Supported: `examples/heap-object/` | Supported: `tests/cpp_import.rs::locked_cpp_branch_and_early_return_verify_through_the_shared_sidecar_path` | Supported: `tests/rust_import.rs::rust_moves_drop_effect_and_return_capture_verify` |
| Loops | Supported: `while`, `do`, `for`, `break`, `continue`, with invariants; `mdtests/c_while_break_continue.md` | Not supported: only a literal `do { } while (0)` wrapper | Partial: `while`, slice and array `for`, `chunks_exact`; no `loop`, `break`, `continue`, or labels; `examples/rust-loops/` |
| `switch` and `match` | Partial: literal case labels only; `mdtests/c_switch.md` | Not supported | Not supported |
| `goto` | Partial: forward `goto` and single-entry natural cycles; not mixed with loops; `mdtests/forward_goto_cleanup_chain.md` | Not supported | Not applicable |
| Recursion | Supported: with a `decreases` measure, including mutual recursion; `mdtests/c_decreases_mutual_recursion.md` | Not supported: refused at import | Not supported: not documented or exercised by any fixture |
| Termination | Supported: proved by default; `diverges` opts out; `mdtests/c_decreases_loop.md` | Supported: no loops or recursion are admitted; `examples/basic-cpp/` | Supported: `decreases` on `while` loops; `examples/rust-loops/` |
| Direct calls and modular contracts | Supported: `examples/multifile-registry/` | Supported: `tests/fixtures/cpp-verification/direct-call/` | Supported: `examples/basic-rust/` |
| Function pointers and callbacks | Partial: known targets dispatch; an abstract target needs a named contract; no callback arrays; `mdtests/c_named_function_contract.md` | Not supported | Not supported |
| Dynamic dispatch (virtual functions, trait objects, closures) | Not applicable | Not supported | Not supported |
| Exceptions, unwinding, non-local exits | Not supported: `setjmp` and `longjmp` | Partial: one `int` payload, `catch (int)`, `noexcept` guards; `mdtests/cpp_two_guard_unwind.md` | Not supported: `panic=abort`; panics are proved absent, not handled |
| Variadic functions | Not supported: prototypes only; `mdtests/c_variadic_call_rejected.md` | Not supported | Not applicable |
| Inline assembly | Partial: the Linux `barrier()` only; `mdtests/c_asm_memory_barrier.md` | Not supported | Not supported |

## Runtime errors checked

A cell here is Supported when the verifier refuses a proof whose execution can
reach the error under the stated requirements. The cited fixture is usually a
refusal.

| Error | C | C++ | Rust |
| --- | --- | --- | --- |
| Signed overflow (Rust: arithmetic overflow panic) | Supported: `mdtests/overflow.md` | Supported: `tests/cpp_import.rs::signed_scalar_arithmetic_rejects_undefined_operations_and_false_claims` | Supported: `tests/rust_import.rs::rust_checked_arithmetic_requires_a_panic_freedom_bound` |
| Division or remainder by zero, `INT_MIN / -1` | Supported: `mdtests/c_bool_division_by_zero.md` | Supported: `tests/cpp_import.rs::unsigned_division_rejects_zero` | Supported: `tests/rust_import.rs::rust_unsigned_panic_paths_are_rejected` |
| Invalid shift | Supported: `mdtests/c_shift_large_count.md` | Not applicable: shifts are not admitted | Partial: unsigned shifts only; signed shifts refused; `tests/rust_import.rs::rust_and_charon_unsigned_shifts_preserve_full_width_counts` |
| Out-of-bounds access (Rust: index panic) | Supported: `mdtests/pointer_arithmetic_past_a_viewed_range_is_refused.md` | Supported: `tests/cpp_import.rs::cpp_native_size_t_last_load_checks_nonempty_and_actual_backing_bounds` | Supported: `tests/rust_import.rs::rust_fixed_array_indices_reject_panics_before_narrowing` |
| Null dereference | Supported: `mdtests/malloc_outcome_null_arm_dereference_refused.md` | Supported: `tests/cpp_import.rs::cpp_literal_null_pointer_dereference_requires_live_backing_offline` | Not applicable: safe references are non-null |
| Use after free or after lifetime end | Supported: `mdtests/freed_pointer_equality_rejected.md` | Partial: automatic objects only, since no heap is admitted; `tests/cpp_import.rs::cpp_reference_into_destroyed_local_backing_cannot_be_read_offline` | Not applicable: rustc's borrow checker is trusted |
| Uninitialized read | Supported: `mdtests/a_join_leaves_a_local_uninitialized_when_one_arm_does.md` | Supported: `tests/cpp_import.rs::cpp_uninitialized_integer_read_rejects_even_a_reflexive_claim_offline` | Not applicable: rustc rejects it |
| Misaligned access | Partial: retyping casts are refused, and tag-bit arithmetic needs `aligned` evidence; `mdtests/aligned_from_malloc.md` | Not applicable: no retyping casts except to `std::byte*` | Not applicable: no raw pointers |
| Strict aliasing and type punning | Partial: typed loads must match the stored cell; only byte views of integer cells; `mdtests/byte_representation_integer_bytes_as_pointer_refused.md` | Partial: `reinterpret_cast` only to `std::byte*`; `tests/cpp_import.rs::cpp_byte_reinterpretation_profile_refuses_nonbyte_and_reverse_casts` | Not applicable: no `transmute` or unions |
| Write to const or string-literal storage | Supported: `mdtests/string_literals_reject_write.md` | Partial: writes through `const` records refused; no `const_cast`; `tests/cpp_import.rs::class_record_proofs_reject_missing_authority_false_frames_and_readonly_writes` | Not applicable: rustc rejects it |
| Unsequenced side effects | Partial: conflicting forms are refused rather than modeled; `mdtests/c_chained_assignment.md` | Partial: ambiguous sibling effects are refused; `tests/cpp_import.rs::nested_calls_reject_sibling_memory_reads_effects_arithmetic_and_other_calls` | Not applicable: Rust fixes evaluation order |
| Comparing pointers to different objects | Supported: `mdtests/a_one_past_the_end_pointer_is_not_compared_with_another_object.md` | Not supported: pointer comparisons outside equality are not admitted | Not applicable |
| Data races | Partial: under the modeled pthread runtime, workers need exclusive authority; there is no race semantics; `mdtests/authority_modeled_pthread_alias_worker_requires_authority.md` | Not applicable: no concurrency admitted | Not applicable: no concurrency admitted |
| Undefined behavior in `unsafe` code | Not applicable | Not applicable | Not supported: `unsafe` functions and calls are refused at import |
| Explicit `panic!`, `assert!`, `unwrap` | Not applicable | Not applicable | Not supported: macros and generic library calls are refused |

## Provenance

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Pointer identity (block and offset) | Supported: `mdtests/c_pointer_viewable_establishes_provenance.md` | Supported: `tests/cpp_import.rs::mutable_pointer_dereference_and_reference_address_verify_offline` | Supported: `examples/rust-split-at/` |
| Pointer to integer and back | Partial: only a recorded address or zero converts back; `mdtests/cast_masked_word_uses_exact_address.md` | Not supported: nonzero integer-to-pointer casts are refused | Not supported |
| Byte copies of pointers | Partial: `memcpy` keeps allocation identity, grants no authority or lifetime; `mdtests/ext_memcpy_allocation_authority.md` | Partial: `std::as_writable_bytes` keeps identity; `tests/bitcoin_core_money_range.rs::pinned_writable_byte_span_reference_preserves_view_offline` | Not supported |

See [Memory model](../concepts/memory-model.md) and
[Byte representation](../internals/byte-representation.md).

## Libraries

Every library function is an assumption stated by a Click contract. Click
supplies its own declarations; it never verifies a platform library.

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Strings | Partial: ASCII literals, byte-buffer predicates; no wide strings; `mdtests/string_literals.md` | Not supported | Not supported: no `String` or `str` |
| Standard library calls | Partial: `memcpy`, `memcmp`, `memset`, `strlen`, and the allocator family; no stdio; `mdtests/c_builtin_string_and_stdlib_headers.md` | Partial: a catalog for `std::span<int>` and `std::as_writable_bytes`; other calls refused; `tests/bitcoin_core_money_range.rs::axiomatic_span_pop_back_verifies_against_catalog_contracts` | Partial: slice `len`, `split_at`, `iter`, `chunks_exact`, core `From`, `mem::drop`; `examples/rust-chunks-exact/` |
| Your own `extern` contracts | Supported: reported as external assumptions; `mdtests/external_function_contract_call.md` | Not supported: documented for uncatalogued standard functions, but no fixture verifies one | Not supported |

## Concurrency

Concurrency exists only for user-space C under the opt-in `modeled-pthread`
runtime. It is a conditional assumption about any C library that implements
Click's pthread specification.

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Threads | Partial: `pthread_create` and `pthread_join` with null attributes and a direct worker; `examples/concurrency-fork-join/` | Not supported | Not supported |
| Mutexes | Partial: `pthread_mutex_init`, `lock`, `unlock`, `destroy` with null attributes; `mdtests/authority_mutex_control_deposit.md` | Not supported | Not supported |
| Atomics and memory orders | Partial: one-shot release/acquire publication of an `atomic_int`; no read-modify-write, `seq_cst`, or fences; `mdtests/publication_one_shot_handoff.md` | Not supported | Not supported |
| `volatile`, `READ_ONCE`, `WRITE_ONCE` | Partial: sequential meaning only; no atomicity or visibility; `mdtests/sequential_kernel_access_primitives.md` | Not supported | Not applicable |
| Kernel synchronization (RCU, spinlocks), signals, interrupts | Not supported | Not supported | Not supported |

## Preprocessing and static polymorphism

| Feature | C | C++ | Rust |
| --- | --- | --- | --- |
| Preprocessor without a compiler | Partial: object-like macros, function-like macros with up to three parameters, bounded `#if`; `mdtests/function_like_macros.md` | Not applicable | Not applicable |
| Preprocessor through the compiler | Supported: full GCC preprocessing in import mode; `tests/compiler_import.rs::compiler_import_define_changes_require_refresh_and_change_the_proof` | Supported: Clang preprocessing, every opened header locked; `tests/cpp_import.rs::every_opened_header_is_locked_even_outside_the_reachable_graph` | Not supported: macros other than compiler desugaring are refused |
| Headers | Partial: project-local includes and Click's own system headers, also under a compiler import, in GCC's search order; `mdtests/always_inline_functions_in_headers.md`, `tests/compiler_import.rs::compiler_import_project_headers_precede_clicks_in_gcc_search_order` | Partial: real headers parsed; system-header bodies are axioms; `tests/cpp_import.rs::included_header_definition_is_selected_locked_and_validated` | Not applicable |
| Templates and generics | Not applicable | Partial: concrete function and class template instances; no dependent patterns or packs; `tests/cpp_import.rs::concrete_template_instances_have_distinct_identities_and_modular_contracts` | Not supported: type and const generics are refused |
| Traits and operator overloading | Not applicable | Partial: non-virtual methods and `operator[]`; `tests/fixtures/cpp-verification/value-methods/` | Partial: concrete `Drop`, `Default`, assignment-operator, and core `From` impls; `tests/rust_import.rs::charon_assignment_operators_check_lanes_panic_obligations_and_authority` |

## Unchanged upstream source

These are the largest bodies of unmodified third-party source verified so
far. Each claim covers the named functions only.

| Evidence | C | C++ | Rust |
| --- | --- | --- | --- |
| Upstream source verified unchanged | Partial: json-c `json_c_version.c`, pinned zlib entry points, Linux `rb_parent`; Linux `lib/rbtree.c` is not yet verified; `examples/jsonc-existing-source/` | Partial: Bitcoin Core v31.1 `MoneyRange`, `FeeFrac` methods, `GetSizeOfCompactSize`, `SpanPopBack`; `integrations/bitcoin-core-money-range/` | Partial: adler2 2.0.1 constructors, constants, and bounds; the checksum result is not yet proved; `tests/rust_import/crate_inputs.rs::charon_adler2_unchanged_constructor_returns_initialized_state` |

## What no proof covers

In every language, a proof does not cover: stack depth, memory exhaustion, or
other host limits; compiler optimizations beyond the recorded profile; the
platform C, C++, or Rust library; the compiler, Clang exporter, or Charon; and
any target other than x86-64 Linux. See [What Click trusts](../concepts/trust.md).
