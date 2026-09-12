# P1: Basic C++ verification with references and scoped cleanup

## Objective and violated invariant

Requested on 2026-09-11. Planning base: `2ac83e6d`.

Deliver a small, usable C++ verification path before launch. The intended
public claim is: **Click has basic C++ support for a documented, non-throwing
subset with references, simple objects, and scoped constructors/destructors.**
The first additional language is C++; Rust follows later. The rationale and
longer-term architecture live in
[Supporting more languages](../design/supporting-more-languages.md).

Accepting a `.cpp` suffix, compiling C-shaped syntax as C++, or proving a
hand-translated C copy does not meet this objective. An unchanged C++ function
must reach the normal Click verifier with its reference, initialization,
object-lifetime, and implicit cleanup behavior represented in checked rules.
The frontend must reject unsupported semantics rather than erase them.

This is P1 by user direction. The rbtree remains the key launch demo. This
issue establishes the small additional-language path; it does not require
Bitcoin Core, the C++ standard library, a general C++ frontend, or Rust support.

## First supported slice

Use one explicitly pinned Clang toolchain, C++20, and one x86-64 Linux LP64
profile with exceptions and RTTI disabled. Match or explicitly distinguish
Click's existing scalar/layout assumptions; record language mode and compiler
identity rather than calling a C++ import an ordinary C import. The exact
distributable Clang version is selected and pinned in step 1.

| Area | Required in this issue |
| --- | --- |
| Source boundary | A header-free `.cpp` translation unit with user-selected free functions and their reachable definitions. |
| Scalars and statements | `void`, `bool`, 32-bit `int`, integer literals and existing checked scalar operations; declarations, assignments, direct calls, blocks, `if`, and returns. |
| Memory | Pointers to supported live objects, dereferences, field access, and lvalue-reference parameters `T&` / `const T&`. |
| Objects | Simple non-inheriting structs with scalar/pointer fields, a supported explicit constructor, and a non-virtual destructor. No class copies, moves, or class-valued arguments/results. |
| Initialization | Member-initializer lists in declaration order, constructor body execution, and ordinary local object construction. |
| Cleanup | Exactly-once destruction of constructed automatic objects at normal block exit and every early/ordinary return; nested scopes and reverse construction order. |
| Contracts | Surface Click sidecars bound to original C++ declarations, existing `owns`/`views` resources, modular constructor/destructor calls, and value/memory postconditions. |
| Tools | Ordinary verify, source diagnostics, expand/reverify, profile, and audit through the existing bounded engine. |

All reachable calls in this slice must have checked non-throwing bodies or an
explicitly justified supported contract. A `noexcept` spelling or
`-fno-exceptions` alone is not evidence that an unknown external operation
returns normally. Reject reachable `throw`/`try`, unsupported exceptional
paths, unmodeled termination, and missing callees. Preserve the project's
existing explicit boundary for trusted external specifications.

Defer templates, overload sets at the public contract boundary, inheritance,
virtual dispatch, operator overloading, unions, dynamic allocation, temporaries
of class type, reference lifetime extension, class copy/move and copy elision,
exceptions/unwinding, coroutines, threading/atomics, standard-library proofs,
and general `goto`. Unsupported selected code gets a source diagnostic.
These omissions are an explicit subset boundary, not permission to rewrite
an existing C++ implementation until it passes.

## Small intended regression

Verify the original source of this synthetic example:

```cpp
struct Restore {
    int *p;
    int saved;

    explicit Restore(int *slot) noexcept : p(slot), saved(*slot) {
        *p = 7;
    }
    ~Restore() noexcept { *p = saved; }
};

int with_restore(bool early, int &value) noexcept {
    Restore guard(&value);
    if (early) {
        return value;
    }
    value = 9;
    return value;
}
```

The sidecar owns the caller's initialized integer and proves both:

- `result == (early ? 7 : 9)`;
- the referenced integer equals its entry value when the call completes.

Those are semantic requirements, not proposed new sidecar syntax. Finalize
the minimal C++ declaration-binding spelling in step 1. The return value must
be captured before the destructor restores the integer; a claim that the
result always equals the entry value must fail. A modular caller starting
with 41 must get 7 or 9 and still observe 41 afterward.

The constructor's saved-pointer field does not by itself exclusively borrow
the pointee for the object's entire lifetime. The middle assignment to
`value` is valid C++. Constructor and destructor contracts must obtain the
authority needed for their actual calls without inventing Rust alias rules.

Planning evidence: this exact example, with a caller checking both paths and
entry value 41, compiled and exited 0 with Apple Clang 16.0.0
(`clang-1600.0.26.6`) on ARM64 macOS. A header-free Clang CFG inspection under
`--target=x86_64-unknown-linux-gnu -std=c++20 -fno-exceptions -fno-rtti
-funsigned-char -ffreestanding` also succeeded and showed member initialization
and an implicit destructor after return-value evaluation on both paths.
These are compiler observations, not Click proofs, an implemented exporter,
or qualification of a shipping toolchain.

Additional focused regressions:

1. `int&` and `const int&` alias while the first writes and the second reads.
   The existing `design/borrow-probes/alias_and_cleanup.cpp` provides a witness.
   Do not translate `const T&` into an unconditional stable view.
2. Two nested guards write distinguishable values during destruction. Prove
   the correct reverse order on block fallthrough and early return.
3. A branch skips object construction. Its path must not run that object's
   destructor. Include a conflicting destructor precondition to expose an
   accidentally synthesized call.
4. A missing/wrong destructor effect, out-of-bounds pointer operation, and
   false restored-value postcondition are rejected by verification.
5. Unsupported source features and mismatched compiler/target/import identity
   produce local diagnostics and cannot fall back to C parsing.

## Implementation sequence

### 1. Pin the frontend boundary and the claim

- Add a sibling C++ program-language frontend under `src/languages/`, keeping
  Surface Click as the proof language. Audit `C0VerificationSession` and the
  prepared-source inputs in `src/surface/verification.rs`; generalize their
  program input boundary only as needed for the second language.
- Use a small exporter built against the selected Clang LibTooling APIs for
  semantic declarations, types/layout, source locations, and control flow
  including implicit construction/destruction. Give its output a Click-owned,
  versioned schema. Do not parse human-readable AST/CFG dumps in production or
  grow the hand-written C parser into a C++ parser. Clang provides standalone
  semantic tooling through LibTooling.
  [Clang LibTooling](https://clang.llvm.org/docs/LibTooling.html)
- Reuse the existing compiler process bounds and locked-import discipline,
  adapting compiler-specific capture where needed. The current
  `src/languages/c/compiler_import.rs` handles preprocessed C text and GCC
  toolchain details; it is not an existing typed C++ importer.
- Lock source/dependency hashes, exporter schema/version, compiler identity,
  target, language standard, ABI/layout facts, and semantic flags. Carry this
  identity through verification results, certificates, expansion, and caches.
- Bind contracts by resolved declaration identity, with readable source names
  and spans. Define support for reference parameter spelling and generated
  constructor/destructor identities. Do not use mangled names as user-facing
  proof syntax or infer resource guarantees from C++ `const`.
- State the trust boundary: Clang and the exporter/lowering are trusted source
  interpretation, while the kernel checks the modeled operations. A compiler
  dump or successful C++ compilation is not a proof certificate.

### 2. Check object operations and cleanup transitions

- Reuse scalar, memory, resource, and call rules where their semantics match;
  retain the source-language/profile identity. Add explicit checked operations
  for member initialization and begin/end of supported object lifetimes.
- Reference lowering must preserve the supported C++ binding/lifetime
  constraints and referent identity. Loads still check initialization. A
  reference type or a non-null address alone does not grant memory authority,
  and a C++ reference must not inherit Rust's stronger aliasing rules.
- Model constructors and destructors with ordinary checked call contracts and
  their original bodies. Verify those contracts. Implicit invocation must not
  become an assumed postcondition or an unchecked frontend-only side effect.
- Represent return as evaluation/capture of the result, required cleanup
  transitions, and final transfer to the caller. Maintain which automatic
  objects have actually been constructed and destroy them in the required
  order. Preserve cleanup source attribution in certificates and diagnostics.
- Use the same edge/scope abstraction that the
  [goto issue](goto.md) is designing. Normal C++ scope exits can land before
  user-written C goto; this issue does not depend on completing arbitrary
  labels, backward edges, or exception unwinding. Do not encode cleanup with
  proof-only variables or edits to the C++ source.
- Integrate the stable-view rules from [fix-views.md](fix-views.md). A
  destructor must have permission for each write and cannot invalidate an
  outstanding view. Distinguish object lifetime, scope cleanup, and loan
  expiration; they are not interchangeable events.

### 3. Deliver an ordinary proof workflow

- Add a small example project containing the unchanged C++ source, sidecars,
  pinned compiler/import configuration, and reproducible commands. A user can
  verify it without manually translating it to C or running a special hidden
  checker. Add supported-subset and limitation documentation.
- Route verify/profile/expand/audit and fixture tests through the same shared
  bounded engine. Expansion must emit source-level sidecar proofs that reverify
  against the original C++ import. Report implicit operations at their source
  declaration or exit edge, not at invented C lines.
- Provision the pinned compiler/exporter in the gate's supported development
  and CI environments. Missing required tooling fails with a clear setup
  diagnostic; it must not silently skip the C++ fixture or download a compiler
  during tests. Add the fixture to `scripts/check.sh` through the normal harness.

## Acceptance criteria

- The documented subset and original RAII/reference examples verify through
  the normal CLI. Their claims cover functional results and memory effects,
  not just successful parsing or compilation.
- The cleanup-order, skipped-construction, aliasing, false-contract, invalid
  access, unsupported-feature, and stale-import regressions above pass.
- Constructors/destructors are checked modularly, and representative expansion,
  re-verification, profiling, and audit agree. No duplicate verification engine
  or hidden C translation becomes the proof boundary.
- Resource/cleanup operations satisfy the existing efficiency contract. Add
  deterministic multi-size regressions if frontier or state representation
  changes; a fixed call/exit must not scan unrelated functions or old history.
- The shipping profile, trusted frontend boundary, supported constructs, and
  deliberately deferred features are explicit. The support claim is limited
  to this subset; no claim about arbitrary C++, Rust, or compiled machine code.
- Existing C fixtures and `scripts/check.sh` pass. Delete this issue and its
  list entry when the implementation, regressions, and documentation land.

Dependencies: stable borrowing from [fix-views.md](fix-views.md), the existing
shared call/resource transition machinery, and only the edge/scope support
actually needed for normal cleanup. The general multi-target, goto, and Rust
projects do not need to finish to deliver this slice.
