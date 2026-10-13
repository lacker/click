# Extend the C++ standard-library contract catalog

Priority: P2.

Soundness: incomplete. A call with no catalog contract is refused by name.
A library whose layout does not match binds no model accessor
(`model_accessors` in `src/languages/cpp/standard_library.rs`), so libc++
fails closed instead of being misbound. Catalog contracts are trusted axioms,
documented in `docs/concepts/trust.md`.

P2, by user request. The axiomatic standard-library boundary is in place: a
function declared in a system header is an opaque call checked against the
contract Click supplies for it (see
[the C++ standard library](../docs/reference/cli/import.md#c-standard-library)).
The catalog in `src/languages/cpp/standard_library.rs` covers only
`std::span<int>`'s `size`, `data`, `front`, `back`, `operator[]` and `first`,
with the `std_span_data` and `std_span_size` model accessors bound for
libstdc++. Nothing is wrong with what it covers; it is just small.

## Violated invariant

A C++ program inside Click's supported semantics that calls the standard
library is refused at each call without a catalog contract, naming the
function. Ordinary standard-library use (`std::span` of other element types,
`std::array`, `std::optional`, `std::min`/`std::max`, and similar) should
verify against Click contracts without the sidecar stating its own `extern`
assumption for each call.

## Intended regression

- A `std::span<unsigned char>` (or `std::span<const int>`) caller using
  `size`, `data`, `operator[]`, `first` and `last` verifies against catalog
  contracts, so entries are generic over the element type rather than copied
  per instantiation.
- `std::span::last`, `subspan` and `size_bytes`, which Bitcoin Core's span
  helpers use, verify against catalog contracts; today `size_bytes` is the
  regression for a refused uncatalogued call.
- One further type family needed by a real program (for example
  `std::array<T, N>` element access or `std::optional<T>` observers) has
  catalog contracts and model accessors.
- The same accessors bind under libc++ as well as libstdc++, or a libc++
  layout is refused by name rather than misbound.

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
