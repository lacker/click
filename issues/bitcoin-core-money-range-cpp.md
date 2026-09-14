# P2: Verify Bitcoin Core `MoneyRange` under a supported Clang profile

## Objective and violated invariant

After the minimal C++ path in [basic-cpp-support.md](basic-cpp-support.md)
lands, demonstrate that it composes with an unchanged function from a real
C++ project. The intended public claim is deliberately narrow: **Click
verifies Bitcoin Core's original `MoneyRange` function from one pinned
release, using one Bitcoin-supported Clang C++20 build profile.**

A hand-copied function, a simplified reimplementation, a special translation
unit that changes the implementation, or analysis under flags that Bitcoin
does not support would not establish that claim. Likewise, accepting the file
as C-shaped syntax would not exercise the C++ frontend boundary. The selected
declaration, its reachable constants and types, the actual compiler command,
and the imported semantic artifact must remain tied to the pinned upstream
source and profile.

This is P2 because [basic-cpp-support.md](basic-cpp-support.md) owns the P1
architecture milestone and its synthetic reference/cleanup regression. This
issue is the first real-project integration and may extend that initial subset
only where the unchanged Bitcoin function requires it; it does not expand the
P1 launch claim to Bitcoin Core as a whole.

## Pinned target and supported profile

Use Bitcoin Core v31.1, resolving the release tag to an exact commit in the
fixture lock, and select the unchanged inline function in
`src/consensus/amount.h`:

```cpp
typedef int64_t CAmount;
static constexpr CAmount COIN = 100000000;
static constexpr CAmount MAX_MONEY = 21000000 * COIN;
inline bool MoneyRange(const CAmount& nValue) {
    return nValue >= 0 && nValue <= MAX_MONEY;
}
```

Use an actual Bitcoin Core CMake compile command from an x86-64 Linux build,
with an exact Click-pinned Clang release that satisfies Bitcoin Core v31.1's
documented minimum of Clang 17. Bitcoin Core v31.1 requires C++20 with compiler
extensions disabled and documents Clang as a supported alternative to its
default GCC build:

- [Bitcoin Core v31.1 CMake language settings](https://github.com/bitcoin/bitcoin/blob/v31.1/CMakeLists.txt)
- [Bitcoin Core v31.1 compiler requirements](https://github.com/bitcoin/bitcoin/blob/v31.1/doc/dependencies.md)
- [Bitcoin Core v31.1 Unix Clang configuration](https://github.com/bitcoin/bitcoin/blob/v31.1/doc/build-unix.md)

Do not add `-fno-exceptions`, `-fno-rtti`, freestanding flags, replacement
headers, or other verifier-specific build settings unless the selected Bitcoin
target itself uses them. It is sufficient for this function's reachable
semantic graph to contain no throwing operation; this issue does not require
Click to model exception handling merely because the surrounding supported
build profile enables exceptions.

Process the function through a real Bitcoin translation unit and its generated
compilation database. The exporter may select `MoneyRange` and its reachable
declarations without lowering unrelated declarations in that translation
unit. Do not introduce a Click-owned wrapper as the source of the function or
maintain a copied fixture that can silently diverge from upstream.

## Small intended regression

Bind a sidecar contract to the resolved C++ declaration identity for
`MoneyRange(const CAmount&)`. Prove that it performs no write through its
`const CAmount&` argument and returns exactly whether the referenced signed
64-bit value lies in the inclusive interval from zero through `MAX_MONEY`.

Exercise at least these boundary values through modular callers:

1. `-1` returns false;
2. `0` returns true;
3. `MAX_MONEY` returns true;
4. `MAX_MONEY + 1` returns false.

The regression must import the `CAmount` alias, the two `constexpr` constants,
the constant expression defining `MAX_MONEY`, the `const` lvalue reference,
signed 64-bit comparisons, and short-circuit conjunction with their C++
semantics. A deliberately false inclusive-boundary contract must fail normal
verification.

Add focused import failures for a modified upstream header, a changed compile
command or compiler/profile identity, and a declaration selector that resolves
to the wrong overload or source location. None may fall back to the C parser or
continue using a stale semantic artifact.

## Acceptance criteria

- The fixture lock identifies the Bitcoin Core v31.1 commit, unchanged
  `src/consensus/amount.h` content, selected translation unit and compilation
  command, Clang executable/version, C++20 mode, target, sysroot/standard
  library, relevant flags, dependencies, exporter schema, and declaration
  identity.
- An ordinary documented Click workflow verifies the exact range contract and
  the four boundary callers against the upstream function. No handwritten C,
  copied C++, proof-only implementation branch, wrapper definition, or special
  verifier executable is in the verification boundary.
- The importer handles unsupported declarations outside the selected reachable
  graph without claiming support for them. Unsupported semantics reachable
  from `MoneyRange` instead produce a local source diagnostic.
- Normal verify, expansion and re-verification, profile, and audit agree on the
  source/profile identity and result. A false range contract and every stale or
  mismatched import regression are rejected.
- Documentation states the exact supported claim: one function from one
  Bitcoin Core release under one Clang C++20 profile. It does not claim general
  Bitcoin Core, GCC C++, standard-library, exception, or binary verification.
- Existing C and C++ regressions and `scripts/check.sh` pass. Delete this issue
  and its list entry when the upstream fixture, proof, regressions, and
  documentation land.

Dependencies: [basic-cpp-support.md](basic-cpp-support.md). If the P1 schema
cannot represent signed 64-bit aliases, imported `constexpr` integral globals,
or a project compilation command, extend the shared frontend boundary rather
than creating a Bitcoin-specific parser or verifier path.
