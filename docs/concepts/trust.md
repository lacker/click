# What Click trusts

A Click verdict is only as sound as the code and assumptions it rests on. This
page lists them. Read it before you rely on a verified claim, or before you
assess a public claim made with Click.

The short version: Click has no small, independent proof checker. A verdict
rests on Click's own kernel, on the code that turns source claims into kernel
obligations, on its model of C and of the target, and on the contracts you
declare for code that Click does not verify. Smart proof search is not trusted.

## Summary

| Component | Trusted | Approximate size | Where |
| --- | --- | --- | --- |
| Kernel: states, transitions, certification, theorem-producing operations | Yes | 254,000 lines of Rust | `src/kernel` |
| Surface parsing, validation, and lowering of claims into obligations | Yes | Part of 181,000 lines of Rust | `src/surface` (see [Surface](#surface-obligation-construction)) |
| Smart planning and proof search | No | Part of `src/surface` | `src/surface/planning`, `src/surface/proof/smart_*` |
| C front end and target model | Yes | 29,000 lines of Rust | `src/languages/c` |
| C++ and Rust import, with their pinned external front ends | Yes, for those languages | 11,000 and 8,000 lines of Rust, plus a 4,500-line C++ exporter | `src/languages/cpp`, `src/languages/rust`, `tools/cpp-exporter` |
| Standard library theorems | Checked by the gate, then applied without re-checking | 158 theorems in 1,626 lines | `stdlib/prelude.click` |
| `extern` contracts | Yes: assumptions | 5 in the prelude, plus any you declare | `stdlib/prelude.click`, your sidecars |
| CLI rendering and profiling | No: they do not decide validity | 9,500 lines of Rust | `src/bin` |

Line counts exclude test files and inline `#[cfg(test)]` modules, and are
rounded. They were measured on 2026-10-12 and are a guide to scale, not an
audited number.

## The kernel

`src/kernel` defines proof states, checked transitions, and certification. A
`Theorem` is an abstract value that only kernel operations can construct. Every
public kernel function that returns a `Theorem` is an axiom in Click's sense,
even when its Rust name is `prove_*`: about 125 such operations, some of which
are parameterized families (see [Kernel](../internals/kernel.md#trusted-shape)
and the glossary entry for axiom). Fifteen `prove_int32_*` operations are also
exposed as named standard theorems.

The kernel deliberately contains domain-specific reasoning about C memory,
resources, integers, and allocation, so that verification is fast and proofs
are short. The cost is a large trusted kernel. A kernel bug can make Click
accept a false claim.

## Surface obligation construction

Translating an accepted source claim into the right kernel obligation is
trusted. This includes parsing the sidecar, validating it, lowering contracts,
propositions, and resources, and choosing a function's entry state and
symbolic inputs (`initial_call_state` in
`src/surface/lowering/resource_lowering.rs`). Kernel certification checks the
execution evidence against the entry that lowering supplies; it does not redo
that translation. See
[Source obligations and checked evidence](../internals/kernel.md#source-obligations-and-checked-evidence).

Smart planning is not trusted. Search, case planning, smart closures, and
termination proposals can only advance a proof through checked kernel
operations, so a bug there can make a true claim fail to verify but cannot make
a false claim verify.

## The C front end and target

Click verifies C as it models it. The following are trusted:

- Source expansion: `src/languages/c/source.rs` is a small include expander,
  not a full C preprocessor. Unsupported directives are rejected.
- Parsing and C semantics: `src/languages/c/syntax.rs` and its neighbors decide
  what each construct means, including which operations are undefined
  behavior.
- The target model: `src/languages/c/target.rs` fixes the data layout (LP64,
  little-endian, 8-bit `char`) and the predefined macros. The kernel target
  treats plain `char` as unsigned, matching the Linux kernel's
  `-funsigned-char` build; the user-space target treats it as signed, matching
  the x86-64 System V ABI and a default GCC or Clang build, and a compiler
  import passes `-fsigned-char` or `-funsigned-char` to match. A C string
  reaches a specification as `uint8` bytes: under signed plain `char` the
  argument is the explicit byte view `(uint8*)s`, and the kernel reads a byte
  through either character type as the same eight bits. See
  [Supported C](../reference/language/c.md#c-implementation-target).
- Modeled system headers: `src/languages/c/modeled_*.h` declare `memcpy`,
  `memcmp`, `memset`, `strlen`, the allocation functions, and the selected
  pthread and atomic interfaces. They carry no executable semantics; their
  behavior comes from the prelude `extern` contracts and the kernel's
  allocation model.

A verified claim says nothing about a different target, compiler flag set, or
data layout. Click does not discover your compiler flags.

For compiler import, the real compiler's preprocessor selects the source; it is
a trusted dependency, not a formally checked step
([`click import`](../reference/cli/import.md)).

## C++ and Rust front ends

C++ and Rust code reaches Click through pinned external front ends: a Clang
19.1.7 exporter (`tools/cpp-exporter`, built by
`scripts/build-cpp-exporter.sh`) and Charon at the revision recorded in
`src/languages/rust/charon-profile.json`. Clang's typed source semantics,
Charon's translation, and Click's translators from their output are trusted.
C++ system-header functions are axioms checked against Click's catalog
contracts in `src/languages/cpp/standard_library.rs`. See
[Experimental Rust imports](../reference/rust.md).

## The standard library

`stdlib/prelude.click` declares 158 theorems. None is an unproved axiom: the
gate proves every one of them with `verify_standard_library`. Ordinary
verification then applies them as dependencies without re-checking them, so a
prelude theorem is trusted to the extent that the gate that checked it is.

The prelude also declares five `extern` contracts that are assumed, not
proved: `memcpy`, `memcmp`, `memset`, `strlen`, and the internal
`__click_constant_p_unknown`.

## Your assumptions

Some trust comes from the sidecar itself:

- An `extern` contract describes a function Click does not verify. Its
  requirements and guarantees are trusted. `click verify` prints an
  `external assumptions:` line for each verified function that depends on one.
- A `diverges` contract drops the claim that the function returns, so the
  result is partial correctness.
- Requirements are assumptions about callers. A claim about a function says
  nothing about a caller that does not establish them.
- `--allow-sorry` admits proof units whose body is `sorry();` without checking
  them. It is a development switch: its admissions are reported, never recorded
  in incremental baselines, and never enabled by `click audit`, `click
  expand`, or the gate.

## What expansion and audit re-check

`click expand` and `click audit` render smart tactics into explicit proof steps
and verify the result through the ordinary entry point. This catches bugs in
smart search, extraction, and rendering. It does not catch bugs in the kernel,
obligation construction, the C front end, the target model, importers, or
`extern` contracts, because the same code checks the expanded proof.

Click does not serialize proof objects, and there is no independent checker
that re-checks a proof outside Click.

## Example: the rbtree proofs

The rbtree proofs show how these boundaries apply to a real claim. Their
current scope is stated in
[Rbtree launch roadmap](../internals/roadmap.md#current-rbtree-status). Beyond
the trusted base above, they also trust a hand-written header that stands in
for the Linux `rbtree.h` and `rbtree_augmented.h`.
