# Extend the C++ standard-library contract catalog

Priority: P2.

Soundness: incomplete. A call with no catalog contract is refused by name.
A library whose layout does not match binds no model accessor
(`model_accessors` in `src/languages/cpp/standard_library.rs`), so a layout
that matches no binding, or more than one, fails closed instead of being
misbound. Catalog contracts are trusted axioms, documented in
`docs/concepts/trust.md`.

P2, by user request. The axiomatic standard-library boundary is in place: a
function declared in a system header is an opaque call checked against the
contract Click supplies for it (see
[the C++ standard library](../docs/reference/cli/import.md#c-standard-library)).

## Done

The `std::span<T>` entries are generic over the element type. `T` may be
`int`, `unsigned int`, `unsigned char` or `std::byte`; the exporter names
`unsigned char` class template arguments. A dynamic-extent span's `size`,
`size_bytes`, `data`, `front`, `back`, `operator[]`, `first`, `last` and
`subspan(offset, count)` have contracts. `std_span_data` and `std_span_size`
bind for libstdc++ and for libc++'s `__data_` and `__size_` layout.
`tests/bitcoin_core_money_range.rs` covers `subspan`, `last` and `size_bytes`
on `std::span<unsigned char>` and `std::span<unsigned int>` in the gate, and
`data`, `first` and a `std::span<std::byte>` subview nightly. The C++ profile
admits native element references (`int`, `unsigned int`, `unsigned char`,
`std::byte`, possibly `const`) as parameters, results and locals, and reads
and writes a returned element reference directly, so `s[0]`, `s.front()` and
`s.back()` read and `s[i] = v` writes for each element type. Each has an
expanded proof that names no private field, and refusals for a missing
precondition and a false claim. An uncatalogued call (`empty`) is refused by
name.

## Violated invariant

A C++ program inside Click's supported semantics that calls the standard
library is refused at each call without a catalog contract, naming the
function. Ordinary standard-library use should verify against Click
contracts without the sidecar stating its own `extern` assumption for each
call. The remaining gaps are mostly in the C++ profile, not the catalog:

- Compound assignment through a returned reference (`s[i] += v`) is
  refused by the exporter.
- `const`-qualified template arguments (`std::span<const int>`) are refused
  by the exporter.
- Static-extent spans (`std::span<int, 4>`) are refused: libstdc++'s extent
  storage is an empty record.
- A defaulted argument, as in `subspan(1)`, is refused by the exporter.
- `subspan(offset, std::dynamic_extent)` is refused by a kernel defect
  ([bug](../bugs/a-view-returning-call-refuses-a-deferred-precondition.md)).
- `std::array<T, N>` has an array field and `std::optional<T>` a union
  payload, which the C++ record profile refuses.
- `std::as_writable_bytes` covers only `std::span<int>`: function template
  arguments other than 32/64-bit integers are refused by the exporter.
- The libc++ binding is checked against a synthetic layout only; no libc++
  program is imported end to end.

## Intended regression

- A `std::span<const int>` caller using `size`, `data`, `operator[]`,
  `first` and `last` verifies.
- One further type family needed by a real program (for example
  `std::array<T, N>` element access or `std::optional<T>` observers) has
  catalog contracts and model accessors.
- A libc++ program binds the same accessors end to end.

## Acceptance criteria

- Catalog entries are keyed on the standard name and signature and stated
  only through model accessors; no contract or user proof names a library's
  private fields.
- Element type, extent, and constness are parameters of an entry, not
  separate copies; an instantiation the catalog cannot express is refused
  by name.
- Each new entry has positive coverage through a real program (Bitcoin Core
  where it applies) and a refusal for a false claim or a missing
  precondition, with expanded proofs printing accessor spellings.
- Contracts for calls back into user code (comparators, `std::function`) and
  throwing contracts stay out of scope until an example needs them.
- Documentation lists the catalog, and `scripts/check.sh` passes.
