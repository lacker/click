# A resource on an array element of a C++ reference record does not lower

Soundness: sound. A resource clause that should be accepted is refused.
Nothing false verifies.

## Violated invariant

A resource clause may name one element of a record's inline array field, as
`views a->elems[1];` does for a C struct pointer. For a C++ record reached
through a reference parameter, the same clause fails to lower, although
`views a;` (the whole object) and reading `a._M_elems[1]` in a postcondition
both work. The proof author has to claim the whole object to read or write
one element.

## Reproduction

With the pinned Bitcoin Core fixture (`pinned_span_fixture_with_exact_dependencies`
in `tests/bitcoin_core_money_range.rs`) and dependencies
`sysroot/usr/include/c++/12/array` and
`sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h`:

```cpp
#include <array>
int probe(std::array<int, 4>& a) noexcept { return a[1]; }
```

```click
verifying "span-probe.cpp";
int32 probe(struct array__int__value_unsigned_long_4& a) {
    views a._M_elems[1];
    ensures result == a._M_elems[1];
} by { execute(); simp(); }
```

Verification is refused with:

```text
could not lower `read` resource: the kernel evaluation produced no path:
every evaluation path ended in a runtime error: type mismatch (segment *&a[1])
```

The model-accessor spelling, `views std_array_data(a)[1];`, fails the same
way. Replacing the clause with `views a;` verifies. The plain C version
verifies:

```c
struct arr { int elems[4]; };
int probe(struct arr *a) { return a->elems[1]; }
```

```click
verifying "a.c";
int32 probe(struct arr* a) { views a->elems[1]; ensures result == a->elems[1]; } by { execute(); simp(); }
```

## Acceptance criteria

- The C++ reproduction verifies with `views a._M_elems[1];` and with
  `views std_array_data(a)[1];`.
- A write through `a[1]` verifies with `owns std_array_data(a)[1];` and is
  refused with `views std_array_data(a)[1];`.
- The segment in any such refusal prints the field path, not `*&a[1]`.
