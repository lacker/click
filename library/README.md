# The Click library

The Click library is one Click module per file in this directory, listed
here in library order. A file sees the implicit modules, the modules it
imports with `import click::...;`, and the modules those import:

| Module | Seen | Contents |
| --- | --- | --- |
| `separation.click` | `import click::separation;` | Explicit separation-under-containment axiom over `Resource` descriptors |
| `primitives.click` | implicit | Verifier primitives, part of the language: the abstract resources the kernel interprets (`mutex_guard`, `mutex_live`, `mutex_use`, `publisher`, `subscriber`, `authority`, `allocation`) |
| `nat.click` | implicit | `Nat`, `to_nat`, `nat::add` and their laws |
| `list.click` | implicit | `List<T>`, `list::append`, `list::contains`, `list::length` and their laws |
| `option.click` | implicit | `Option<T>`, the value of a Rust `Option` |
| `result.click` | implicit | `Result<T, E>`, the value of a Rust `Result` |
| `permutation.click` | `import click::permutation;` | `permutation::count`, generic over the element type, and `permutation::permutation` over `int32[]` |
| `bytes.click` | `import click::bytes;`, or with `c/string` | `bytes::count`, `bytes::equal` and the other byte-range predicates over `uint8[]` |
| `cstr.click` | `import click::cstr;`, or with `c/string` | C-string predicates and theorems, and the C-string resource `cstr_at` |
| `c/builtins.click` | implicit | Verifier primitive `__click_constant_p_unknown`, the value of `__builtin_constant_p` |
| `c/string.click` | when the C declares or calls one of its functions | `memcpy`, `memcmp`, `memset` and `strlen` contracts |
| `c/stdio.click` | `import click::c::stdio;`, or with the projected `<stdio.h>` | Stream ownership and write history |
| `integer.click` | `import click::integer;` | `integer::` order, increment and definedness lemmas over native integer widths, `to_integer` bridges for native arithmetic, unsigned wrapping operations, and `Integer` division laws |
| `format.click` | `import click::format;`; the C front end's `snprintf` contracts name it by path | `format::decimal_length`, `format::decimal_digit` and the other decimal rendering functions `printf` writes, with evaluation theorems |
| `rust/i8.click` ... `rust/usize.click` | `import click::rust::u32;`; the integer-method contracts of `rust/integers.click` name them by path | One module per Rust integer type: `u32::min`, `u32::checked_add` and the other core methods the importer specifies, and the Rust names of the lemmas a Rust proof applies (`u32::multiply_to_integer`) |
| `cpp/span.click` | appended to a C++ sidecar when an import calls one of its methods | `std::span<T>` and static-extent `std::span<T, N>` contracts, as template methods written out at each called element type and extent |
| `cpp/array.click` | appended to a C++ sidecar when an import calls one of its methods | `std::array<T, N>` contracts, with each element accessor's `const` and mutable overload as two template methods |
| `cpp/as_writable_bytes.click` | appended to a C++ sidecar when an import calls it | The `std::as_writable_bytes<T, N>` contract, a function template written out at each called instance |
| `rust/vec.click` | `import click::rust::vec;` | The primitive type `Vec<T>`, its bodyless operations and their trusted axioms |
| `rust/slice.click` | `import click::rust::slice;` | `Slice<T>`, a Rust slice as its data pointer and length |
| `rust/core.click` | appended to a Rust sidecar when an import calls one of its methods | The `Vec`, `slice::swap` and `Option`/`Result` unwrapping contracts, as generic `extern fn` blocks written out at each called type; a block no call names is dropped |
| `rust/integers.click` | the line of each integer method an import calls is appended to its Rust sidecar | One-line `extern fn` contracts of the integer core methods, `u32::min`, each stating its result with the function of the same path in `rust/<type>.click` |

Each declaration is in one layer, which sets its trust:

- **Verifier primitives** (`primitives.click`, `c/builtins.click`) are part of
  the language. The kernel or the C front end gives them their meaning; they are
  written here only so the parser declares them. The language reference
  documents them (`docs/reference/language/index.md#verifier-primitives`), with
  `primitive.` inventory IDs.
- **Language library interfaces** are assumed `extern` contracts for the C,
  C++ or Rust library the verified code calls: `c/`, `cpp/`, `rust/core.click`
  and `rust/integers.click`. How they are designed and added is in
  [library interfaces](../docs/concepts/library-interfaces.md); each is listed
  in [trust](../docs/concepts/trust.md#library-interfaces).
- **The specification library** is every other module: checked types, pure
  functions, predicates and theorems, plus the trusted `rust/vec.click` axioms.

`integer::uint64_product_bound_from_division` turns the native nonzero-divisor bound
`x <= 18446744073709551615u64 / y` into an exact Integer product bound. Combine
it with `integer::uint64_multiply_to_integer` for checked unsigned multiplication.

The implicit set is `IMPLICIT_LIBRARY_MODULES` in
`src/surface/validation/declaration_expansion.rs`. The C front end records
the modules a program's declarations and calls bring
(`library_contract_module` in `src/languages/c/syntax.rs`). A module lists the earlier
modules its declarations use with its own `import click::...;` lines.
Built-in tactics apply library theorems whatever a file imports; a library
theorem's verifier identity is its qualified name, `click::module::name`,
so a file theorem may share its bare name (`library_theorem_identity` in
`src/surface/parser.rs`). Imports gate the declarations a file names. A
library module's own proofs are checked against the whole library.

Each module is parsed with the declarations of the modules before it, and
its diagnostics name its own file and line. Types, pure functions, and
theorems use ordinary Click declarations. Ordinary library theorems have checked
proofs. The Integer order axioms `add_le`, `le_antisymmetric`, `lt_step_le`, `multiply_order_nonnegative`, and
`round_down_le` are trusted declarations, used through ordinary explicit application.
The unsigned address-word laws expose bitmask and modular addition identities,
and scalar pointer address offsets at their exact element/index widths. Their
foundational axioms are trusted; alignment weakening and masked-tag helpers are
proved. Expansion cites the alignment and literal-mask guards explicitly.
Kernel standard theorems (13 machine-integer laws including `integer::uint32_from_le_bytes`, 5 Integer truncation laws, 6 `Nat`
laws and 15 separation laws including `separation::separate_restrict`) are backed by
trusted kernel constructors. Their declarations must match the corresponding kernel
axioms exactly. The `extern` contracts are knowns, listed in
[trust](../docs/concepts/trust.md).

A module is named by a `click::` path that mirrors its file:
`import click::cstr;` is `cstr.click` and `import click::c::string;` is
`c/string.click`. A declaration's qualified name adds its own name:
`click::cstr::len`, or `cstr::len` once the module is in scope
(`src/surface/parser/library_paths.rs`).

The library is checked on its own, like any dependency: `verify_standard_library`
proves every library theorem that has a proof, checks each kernel standard
theorem's declaration against its kernel builder
([trust](../docs/concepts/trust.md#the-click-library)), and the gate
runs it in `standard_library_theorems_are_proved_by_their_own_entry_point`. Verifying a
sidecar applies library theorems as dependency declarations and proves only
the sidecar's own theorems. Whole-contract certification accepts a pure theorem
only with kernel authority from a checked proof, so a C proof that cites one of
the few library theorems that certification consumes checks that cited theorem
once during its verification.

For a library addition:

- Add the declaration to the module for its topic. A new module needs an
  entry in `CLICK_LIBRARY_MODULES` in `src/surface.rs`, after every module it
  uses.
- Put positive and negative client examples in `mdtests/`. List clients live
  in `stdlib_list*.md` and should use the implicit library, not redeclare it.
- Add a checked use to `mdtests/stdlib_every_symbol.md`.
- Copy the exact declaration into its module's section of
  `docs/reference/library/index.md` and add its entry to
  `docs/reference/inventory.toml`. A verifier primitive instead goes in the
  language reference as inline code, with a `primitive.` inventory ID. A module in
  `QUALIFIED_MODULES` lists its functions, predicates and theorems by
  in-scope path, `library.function.bytes::count`. The documentation gate checks
  these against the source.
- Run a focused fixture check, then the full `scripts/check.sh` gate. Add
  expansion coverage when exercising a new proof path.

Generic proofs are verified for each concrete instance when used. Exercise
different element families explicitly; a test at `int32` does not check every
possible instantiation. The list fixtures cover scalar and pointer elements
and append over nested lists. The library reference documents current limits.
