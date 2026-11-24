# What Click trusts

A Click verdict is only as sound as the code and assumptions it rests on. This
page lists them. Read it before you rely on a verified claim, or before you
assess a public claim made with Click.

The short version: Click has no small, independent proof checker. A verdict
rests on Click's own kernel, on the code that turns source claims into kernel
obligations, on its model of C and of the target, and on the contracts you
declare for code that Click does not verify. Smart proof search is not trusted.

The trusted base is this large by choice, for now. A false acceptance, once
found, is fixed first: it is a bug, tracked in `bugs/`. Proving the kernel
sound as a whole is separate work, such as an independent proof checker and a
written semantics, and it is not a current priority. Click's priorities are
performance at the scale of large real-world projects, then completeness on
such projects, both measured in practice on real code rather than in theory. Both
are longer-term work, after those priorities (maintainer, 2026-10-14 and
2026-10-17).

## Summary

| Component | Trusted | Approximate size | Where |
| --- | --- | --- | --- |
| Kernel: states, transitions, certification, theorem-producing operations | Yes | 254,000 lines of Rust | `src/kernel` |
| Surface parsing, validation, and lowering of claims into obligations | Yes | Part of 181,000 lines of Rust | `src/surface` (see [Surface](#surface-obligation-construction)) |
| Smart planning and proof search | No | Part of `src/surface` | `src/surface/planning`, `src/surface/proof/smart_*` |
| C front end and target model | Yes | 29,000 lines of Rust | `src/languages/c` |
| C++ and Rust import, with their pinned external front ends | Yes, for those languages | 11,000 and 8,000 lines of Rust, plus a 4,500-line C++ exporter | `src/languages/cpp`, `src/languages/rust`, `tools/cpp-exporter` |
| Click library theorems | Proved ones are checked by `verify_standard_library`; kernel standard theorems are trusted kernel builders whose declarations it shape-checks. All are then applied without re-checking | 220 theorems, 41 of them kernel standard, in 9,658 lines | `library/` |
| Library interfaces: contracts for code Click does not verify | Yes: assumptions | Eight families, each reported by `click verify` ([Library interfaces](#library-interfaces)) | `library/c/`, `src/languages/c/`, `src/languages/cpp/standard_library.rs`, `src/languages/rust/standard_library.rs`, your sidecars |
| CLI rendering and profiling | No: they do not decide validity | 9,500 lines of Rust | `src/bin` |

Line counts exclude test files and inline `#[cfg(test)]` modules, and are
rounded. They were measured on 2026-10-12 and are a guide to scale, not an
audited number.

## The kernel

`src/kernel` defines proof states, checked transitions, and certification. A
`Theorem` is an abstract value that only kernel operations can construct. Every
public kernel function that returns a `Theorem` is an axiom in Click's sense,
even when its Rust name is `prove_*`: about 90 such operations, some of which
are parameterized families (see [Kernel](../internals/kernel.md#trusted-shape)
and the glossary entry for axiom). Some of them are also exposed as the kernel
standard library theorems below. `separation::separate_restrict` is likewise a named
trusted axiom, implemented in `src/kernel/separation_laws.rs`: separate parents
and explicit containment premises imply separate parts. Its `Resource`
parameters describe resources without granting ownership.
`separation::viewable_restrict` likewise transfers pure viewability from a
parent to an explicitly contained part, at the same point. `integer::uint32_from_le_bytes`
is backed by `src/kernel/byte_representation_laws.rs`; it relates a defined
unsigned word to its four representation bytes under an explicit
`little_endian()` premise and a readable-word premise. The selected execution
environment supplies the target premise; pure theorems must require it.

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
  argument is the explicit byte view `s as (uint8 *)`, and the kernel reads a byte
  through either character type as the same eight bits. See
  [Supported C](../reference/language/c.md#c-implementation-target).
- Modeled system headers: `src/languages/c/modeled_*.h` declare `memcpy`,
  `memcmp`, `memset`, `strlen`, the allocation functions, and the selected
  pthread and atomic interfaces. They carry no executable semantics; their
  behavior comes from the [library interfaces](#library-interfaces).

A verified claim says nothing about a different target, compiler flag set, or
data layout. Click does not discover your compiler flags.

For compiler import, the real compiler's preprocessor selects the source; it is
a trusted dependency, not a formally checked step
([`click capture`](../reference/cli/capture.md)).

## C++ and Rust front ends

C++ and Rust code reaches Click through pinned external front ends: a Clang
19.1.7 exporter (`tools/cpp-exporter`, built by
`scripts/build-cpp-exporter.sh`) and Charon at the revision recorded in
`src/languages/rust/charon-profile.json`. Clang's typed source semantics,
Charon's translation, and Click's translators from their output are trusted.
A C++ system-header function or a Rust core method is not translated: a
call to one is checked against its [library interface](#library-interfaces). See
[Experimental Rust imports](../reference/rust.md).

## The Click library

The `library/` modules declare 220 theorems. `verify_standard_library`
checks each one, in one of two ways; the gate runs it
(`standard_library_theorems_are_proved_by_their_own_entry_point`):

- **179 are proved.** Their written or default proofs are checked like any
  other proof. They include the `int32` increment, predecessor, order and
  definedness lemmas, the in-range `+` and `-` observation laws at `int32`,
  `int64`, `uint32` and `uint64`, the `uint32` and `uint64` product laws,
  the `uint32` product-guard and remainder laws, and
  the `uint64` order transitivities, the eight `to_*_round_trip` laws (by
  `integer_cast_identity`, which reads `to_integer(to_T(z))` as `z` under
  `T`'s range at every format), and the Rust names of three product
  lemmas (`u32::multiply_to_integer`), each with a pinned proof of explicit
  steps (`close()`, `normalize()`, and
  `apply` of earlier library theorems).
- **41 are kernel standard theorems.** They have no proof. The check is
  only that the declaration's parameters, premises and conclusion match the
  proposition a Rust kernel builder constructs (`prove_*`, mostly in
  `src/kernel/api.rs`); the theorem is then recorded as an axiom
  (`verify_kernel_standard_theorem_axiom` in
  `src/surface/proof/pure_theorems.rs`; `is_kernel_standard_theorem_name`
  lists them). Their soundness rests on those builders, which are part of the
  trusted kernel. They are 13 machine-integer laws in `integer.click`
  (`int32_remainder_to_integer`; the `uint32` and `uint64` divide and
  remainder laws; 16-bit packing; and the
  `uint32_from_le_bytes` byte layout), 7 Integer truncation laws, 6 `Nat`
  conversion laws and 15 separation laws. `separation::separate_elements` and
  `separation::distinct_elements` are generic over their index type, which
  has no rigid C form, so each is checked at each index type its builder
  admits: `int32`, `int64` and `uint64`. `distinct_elements` concludes
  `&p[i] != &p[j]` from `i != j` over the exact scaled offsets that memory
  resolution already reads as equal exactly when the indices are.

Ordinary verification then applies every library theorem as a dependency
without re-checking it, except that a C proof that cites an `int32` library
theorem certification consumes checks that theorem once. A proved library
theorem is trusted to the extent that the check of its proof is; a kernel
standard theorem is trusted to the extent that its builder is.

The library also declares 93 `axiom`s, which are trusted, not proved.
Seven are the laws of the primitive type `Vec<T>` in
`library/rust/vec.click`, which relate its bodyless operations `vec::len`,
`vec::get`, `vec::push` and `vec::set`
([Rust vectors](../reference/library/index.md#rust-vectors)). Finite
sequences of fewer than 2^64 values satisfy them all, so they are consistent.
Rust's iterators need none: the importer holds a slice iterator as the
slice it still covers and a `chunks_exact` iterator as its own fields, and
runs `core`'s code over them. Another is `integer::uint32_difference_decreases_after_increment`: under
`value < bound`, `(0 - value) + (bound - 1)` is below `(0 - value) + bound`
as integers, because neither `bound - value` nor `(bound - 1) - value`
wraps.

`separation::viewable_offset_nonnull` states C11 6.3.2.3p3 for viewed
memory: an address from the start of a nonempty viewable range through one
past its end is not null. Viewability holds only for storage of a live
object, which C never places at the null pointer, and pointer arithmetic
past one beyond an object is already undefined, so every such address is an
object address. An empty range is excluded because C allows a null pointer
with a zero length.

The unsigned address-word library adds thirteen elementary word axioms and thirty
scalar-pointer offset axioms (ten pointee types, with `int32`, `int64` and
`uint64` indices). They state bitwise identities and guarded low/high mask laws over
wrapping `uint64` arithmetic, and the element-width scaling of an address.
Native additions on their right sides are explicitly cast to `uint64`;
these laws do not assert an unbounded Integer sum. The parsed word declarations
are checked by an independent modular arithmetic oracle at small values,
high bits, mask boundaries and wrapping endpoints. The neutral-bit and
alignment-weakening helpers are proved. Applications keep the exact alignment
and mask guards; no axiom grants memory access or changes a read's identity.

Four elementary Integer multiplication axioms in `library/integer.click`,
`multiply_commutative`, `multiply_negate`, `multiply_add`, and
`multiply_associative`, state commutativity, sign propagation, distributivity,
and associativity. They expose these mathematical identities as named
library applications. Product interval bounds and multiplication order for
nonpositive factors are proved from these equations and the existing order
laws. The independent BigInt oracle checks the new declarations across
negative, zero, positive, and large operands.

Five foundational Integer order axioms in `library/integer.click` expose
rules that ordinary arithmetic proofs already used: `add_le` adds two
inequalities; `multiply_order_nonnegative` preserves order when scaling by a
nonnegative factor; `round_down_le` concludes `value <= bound` from
`0 < divisor`, `remainder < divisor`, and
`value * divisor <= bound * divisor + remainder`; and `le_antisymmetric`
concludes equality from opposite non-strict Integer bounds. The scaling
declaration previously had a certificate proof; it is now trusted directly.
The `lt_step_le` axiom states Integer discreteness: `a < b` implies
`a + 1 <= b`. Its reverse and the non-strict-bound-plus-disequality rule
are proved theorems. Addition, rounding, antisymmetry, and discreteness are
new declarations. Their stated guards and conclusions have an independent
BigInt oracle regression, including negative and arbitrary-width values.

The six floating-point order axioms in `library/float_order.click` give
transitivity for two non-strict comparisons and for either order of a strict
and a non-strict comparison. Each premise is a true IEEE comparison, so the
operands are ordered values. No separate finiteness hypothesis is needed.
The same laws apply to infinities and to both zeros.

The rounded addition axioms in the same module compare a sum with the sum
of its two finite lower or upper endpoints. The ordered premises exclude
NaNs. For an upper bound the finite endpoints rule out positive infinity
in the inputs, and for a lower bound they rule out negative infinity.
Neither case admits a sum of infinities of opposite sign. Each sum rounds
at the law's stated precision.
The float32 scaling axioms multiply both sides of an ordered comparison
by one finite positive factor and round both products at float32 precision.
A positive finite factor excludes both zero-times-infinity and
infinity-times-zero.

Only the built-in library modules may declare a primitive `type`, a bodyless
`function` or an `axiom`; the parser refuses each in any other file. The
kernel reads each instance of a primitive type as a rigid type, so no
constructor case, `match` or induction follows from its having no written
constructors.

## Library interfaces

How a library interface is designed and added, and where Click still departs
from that design, is in [library interfaces](library-interfaces.md). This
section lists what each one assumes.

A library interface is the contract Click assumes for code it does not verify:
a C library function, the allocator, a C++ standard function, a Rust core
method, the thread runtime, or a function you declare `extern`. Every call
is checked against the model; that the real code meets it is assumed, not
proved. Each family is an assumption in the same sense:

| Family | Reported as | What is assumed | Where it is stated |
| --- | --- | --- | --- |
| Your `extern` contracts | `extern` | Each `extern` block a sidecar declares | Your sidecars |
| C library | `C library` | `memcpy`, `memcmp`, `memset` and `strlen` meet their contracts | `library/c/string.interface.click` |
| Allocator | `allocator` | `malloc`, `calloc`, `realloc` and `free` behave as the kernel's allocation model: a fresh block or null, released once | Built in, as a language primitive: the C front end and the kernel (`allocation` resource), documented in [heap allocation](../reference/language/c.md#heap-allocation) |
| Formatted output | `snprintf` | One contract per `snprintf` format a program uses, written from the format ([formatted output](../reference/language/c.md#formatted-output)) | `src/languages/c/formatted_output.rs` |
| Formatted stream output | `printf` | The `fprintf` transition on the hosted `stdout` stream | `library/c/printf.interface.click` |
| Formatted stream output | `fprintf` | The same transition on the stream identified by the `FILE *` argument, for a format of ordinary characters and `%%`, stated with `click::c::stdio`'s format functions | `library/c/fprintf.interface.click` |
| C++ standard library | `C++ std` | The catalog contract of each `std::span`, `std::array`, `std::as_writable_bytes` and selected `std::vector` function an import calls, plus the C++ `memcpy` interface, and the explicitly pinned opaque exception constructor in the `ios_failure` profile | `library/cpp/span.interface.click` (`std::span<T>` and static-extent `std::span<T, N>`), `library/cpp/span_state.click` (logical descriptor state), `library/cpp/span_state_contracts.interface.click` (logical copy construction and `empty()` for dynamic `std::span<int>`), `library/cpp/array.interface.click` (`std::array<T, N>`, its `const` and mutable overloads), and `library/cpp/as_writable_bytes.interface.click` (`std::as_writable_bytes<T, N>`), `library/cpp/vector.interface.click` and `library/cpp/vector_state.click` (logical descriptor, read-only queries, and const subscript of an existing byte vector), `library/cpp/memcpy.interface.click` (byte copy through native `void*` parameters), and Click templates written out at each called element type and extent; `src/languages/cpp/standard_library.rs` keeps the name table and the opaque exception factory contract |
| Rust core library | `Rust core` | The contract of each core method an import calls: integer methods (`u32::min`), `Vec`, slice, and `Option`/`Result` unwrapping ([core library methods](../reference/rust.md#core-library-methods)), with the 7 `axiom`s above | `library/rust/core.interface.click` (`Vec`, `slice::swap<T>`, `Option`/`Result` unwrapping contracts, generic contracts written out at each called type, with only a name table in `src/languages/rust/standard_library.rs`) and `library/rust/integers.interface.click` (one contract per integer method and type, stating its result with the specification function of the same path in `library/rust/<type>.click`; only the called methods' lines are appended) |
| Verifier primitive | `primitive` | `__click_constant_p_unknown`, the value of `__builtin_constant_p`, is 0 or 1 ([verifier primitives](../reference/language/index.md#verifier-primitives)): it stands for a compiler decision, not a library function | `library/c/builtins.interface.click` |
| Thread runtime | `runtime` | The selected `modeled-pthread` specification: create/join, shared mutex calls and one-shot atomic publication obey it | `src/languages/c/thread_runtime.rs` |

The hosted C target supplies a stable, nonnull standard output handle when
the program uses Click's projected `<stdio.h>`. Startup can hand one
stream resource for that handle to `main`.
[Hosted standard output](../reference/language/c.md#hosted-standard-output)

The C++ `ios_failure` profile assumes that constructing the pinned
`std::ios_base::failure(const char*, const std::error_code& = ...)`
returns a fresh opaque value of that exact type, with no caller-observable
memory effects. Its message, representation and `what()` are unavailable to
proofs. The runtime owns the exception storage and its trusted standard-library
destruction. Allocation failure terminates, so `std::bad_alloc` does not
propagate; running without that behavior is outside this profile. The
constructor and its default argument are an explicit library assumption, not
a verified implementation. Internally the model is the reserved external
`__click_cpp_decl_ios_failure`, reported as `C++ std` when called.

A Rust core contract states the method's result with the library function
of the same path in `library/rust/`, `click::rust::u32::min`, and so trusts
that the library function is the method Rust runs; the functions themselves
are ordinary Click definitions, and `mdtests/stdlib_every_symbol.md` checks
each at the edge of its type. The `Vec` contracts also assume that pushing
past `u64::MAX` elements, the model's bound, cannot happen before Rust's own
allocation limit aborts.

`click verify` reports every model a verification relied on in one place: an
`assumptions:` line for each verified function, its models grouped by the
tags above, after one `assumptions: every function -> runtime: ...` line when
the sidecar selects a thread runtime
([`click verify`](../reference/cli/verify.md#output-and-exit-behavior)).
The gate checks that this table names every family the report can print,
every program contract the C library declares, and each `library/cpp/` and
`library/rust/core.interface.click` file in its family's row; the contracts of those
files are listed one by one in the
[library reference](../reference/library/index.md#c-standard-library-interfaces).

## Your assumptions

Some trust comes from the sidecar itself:

- A function contract in an interface file is an assumption about the
  implementation. Click checks its requirements at calls and reports the
  contract with the other [interfaces](#library-interfaces) the proof uses.
  An inline `extern` contract has the same trust semantics during migration.
- A `diverges` contract drops the claim that the function returns, so the
  result is partial correctness.
- Requirements are knowns about callers. A claim about a function says
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
library interfaces, because the same code checks the expanded proof.

Click does not serialize proof objects, and there is no independent checker
that re-checks a proof outside Click.

## Example: the rbtree proofs

The rbtree proofs show how these boundaries apply to a real claim. Their
current scope is stated in
[Rbtree launch roadmap](../internals/roadmap.md#current-rbtree-status). Beyond
the trusted base above, they also trust a hand-written header that stands in
for the Linux `rbtree.h` and `rbtree_augmented.h`.

The divisor-sign laws `integer::quotient_negate_divisor` and
`integer::remainder_negate_divisor` are registered local truncation laws:
for a nonzero divisor, changing its sign negates the quotient and preserves
the remainder. Their constructors read only the two explicit Integer operands.
The signed, arbitrary-width BigInt oracle checks both laws. Named positive-divisor
quotient bounds and interval bounds are ordinary proofs from truncation,
remainder, rounding, and order laws; they add no interval axioms.

Distributivity (`multiply_add`) and multiplication associativity
(`multiply_associative`) are explicit Integer axioms. Distributivity previously
used normalization as its proof. Their declarations have independent signed
arbitrary-width BigInt oracle checks. Coefficient and polynomial expansions
apply these laws and derived orientation/sign lemmas; quotient shifts are
proved from truncation, remainder bounds, and ordinary order laws.

The bounded signed-residue translation emitter uses the proved
`nonnegative_remainder_from_reconstruction` helper, derived from the quotient
reconstruction and truncation identities. It adds no axioms.

The scalar `integer::*_pointer_translate_int32` and
`*_pointer_translate_uint64` families add twenty concrete axiom declarations:
two law shapes at ten scalar pointee types. A selected pointer equality and
an exact Integer displacement equality give the translated pointer equality
at that same element type. No pointer relation follows from wrapping address
words. Parsed declarations have independent BigInt coordinate-model checks
with block/domain variation and multiple strides. The twenty association
helpers are proved from these laws and existing addition observation theorems.
Signed overflow and unsigned wrapping guards are explicit arithmetic obligations;
no law grants memory access or changes a memory state or version point.
