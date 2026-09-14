# Limitations and compatibility

This page lists boundaries that agents should not silently assume away.

## Surface syntax nesting is bounded

Click accepts at most 16 simultaneously nested pairs of parentheses in a
sidecar. Deeper input receives a source-positioned parser diagnostic before
recursive descent begins. This bound covers grouped propositions, grouped
contract expressions, calls, and the other parenthesized surface forms.

## C0 is small

Click does not parse general C. See [Supported C0](c0.md). Missing
features include broader structs, pointer and array forms of 64-bit and
`size_t` integers, signed `char` and wider string-literal forms, unmodeled allocator
compatibility, and some
operators. Supported scalar file-scope globals are described in [Supported
C0](c0.md). The
supported `switch` slice is intentionally narrow: labels must be direct integer
or character literals in one compound body, with no `goto` or arbitrary
constant-expression labels yet.

C0 supports `sizeof` for the modeled scalar and pointer types, plus
`malloc(sizeof(struct T))` into a matching `struct T*` and runtime-sized
`int32` backing allocations such as `malloc(count * sizeof(int32))`, with
ordinary null checking and `free`. The zeroed variants are
`calloc(count, sizeof(int32))` and matching
`calloc(count, sizeof(struct T))` for a `struct T*` target. Compatible
external allocator declarations may describe a supported data-pointer or
pointer-array result with `allocation(result, bytes)` and an owned result
range. Zero sizes, arbitrary byte layouts, `size_t`, allocator results
declared as `void *`, unrelated custom allocator APIs, and `realloc` remain
outside this surface description. Opaque `void *` identity conversions are
supported, but dereference, indexing, arithmetic, and ownership through an
untyped pointer are not.

Plain `char *` and `unsigned char *` remain distinct for implicit conversions
and function signatures. Explicit casts between these one-level byte pointers
are supported and preserve pointer provenance. Casts between `char **` and
`unsigned char **` remain unsupported; sharing byte storage does not make their
pointer cells interchangeable.

Struct support is partial; the [struct subset](c0.md#struct-subset) defines
its current type and layout boundary. Supported records include scalar and
pointer fields, named enums, fixed-dimensional scalar arrays, embedded structs,
and fixed-dimensional embedded-struct arrays. Member access, local arrays, and
array parameters preserve the documented LP64 field offsets, array strides,
and tail padding. Address-taking preserves the containing allocation and the
selected field's ABI offset.

Copyable structs use fresh address-backed storage for parameters, locals,
assignments, and returns. Copies preserve nested fields and array elements;
data-pointer fields retain the same pointee rather than copying it. Supported
function-pointer fields also copy their value and signature. A struct may
contain a supported named read-only union; copies preserve its overlapping
typed member views rather than treating them as disjoint fields. Direct
whole-union values and union-member writes remain unsupported.

Whole-struct lvalue copies and pointer-backed aggregate returns are supported,
including field-wise return postconditions. Positional and designated local
initializers support the documented nested fields and fixed-dimensional local
struct arrays, with zero-filled omitted elements. Supported conditional
aggregate expressions require matching struct types and copy only the selected
branch. Static-storage positional and designated initializers, including
function addresses in callback tables, are supported for the shapes described
in [file-scope objects](c0.md#file-scope-scalar-globals) and the struct
reference. Automatic/local const aggregates,
whole-union initialization, and broader aggregate initializer forms remain
outside the documented subset.

A callback field keeps its declared signature. A load from a provably identified
static callback table yields the concrete function address; an abstract loaded
callback needs an applicable named contract. Writes to a const table remain
rejected. A bare function designator decays to the same address as `&name` in
value positions when that function is declared in the translation unit.

Packed layout, bitfields, and other compiler-dependent layout rules remain
outside the single-profile baseline; `issues/multiple-compilers.md` tracks that
work. Named enum fields use the four-byte scalar ABI representation; broader
enum shapes remain outside the documented subset. Click resource clauses can
name supported fields and embedded aggregate places with their typed byte
ranges. This aggregate-shape support does not complete the separate stable-view
or general resource-transition projects.

## External C functions

Sidecars may declare body-less C callees with `extern` contracts. The kernel
applies those contracts as explicit assumptions, so the callee implementation
is not checked by Click and its preconditions remain caller obligations. The
standard library includes narrow byte-oriented contracts for `memcpy`,
`memcmp`, `memset`, and `strlen`. `click verify` reports the transitive external
assumptions used by each verified function. These contracts still describe
only the supported C0 types; `void *` dereference or ownership, `size_t`,
overlap semantics, and unbounded string loadability remain outside the model.

A verifying source may contain multiple function definitions and compatible
forward prototypes. Project-local quoted includes such as
`#include "include/types.h"` are resolved relative to the including source when
the named header is supplied in the source bundle. Headers may contain
supported structs, typedefs, enums, prototypes, and `static inline` or
`static __always_inline` function bodies. Those inline bodies are checked from
the expanded translation unit and
their calls execute the checked body directly, on the caller's own memory
and resources, with no contract boundary. A sidecar contract may name an
inline helper by its ordinary C spelling for direct verification, but is not
applied as a call boundary. Every call executes the header body; Click
never emits a standalone definition or selects an external one, matching
the observable `always_inline` behavior under the single supported
`x86_64-linux-kernel` profile. Termination follows that execution: a helper
is a node of the caller's call graph rather than an opaque callee, so a
straight-line helper needs no ranking of its own and a ranked loop may call
one, while a helper carrying a loop still needs that loop ranked and a
recursive helper needs a checked rule for its cycle. `extern inline` has profile-dependent
emission rules and stays rejected, as do bare `inline` and other inline
spellings. The declaration-only GNU spellings
`__attribute__((always_inline))` and `__attribute__((__always_inline__))` are
accepted on those helpers; other attributes and function definitions in headers
remain unsupported. The exact trailing struct spelling
`__attribute__((aligned(sizeof(long))))` (and `__aligned__`) is supported as an
LP64 eight-byte alignment requirement; other alignment forms remain
unsupported. Const-qualified static-storage aggregates are read-only, while
automatic/local const aggregates remain unsupported.
System header includes other than the modeled `<stdint.h>`, `<inttypes.h>`,
and `<stdbool.h>`, function-like macros
with more than three parameters, empty arguments, stringification, token pasting,
macro redefinitions without an intervening `#undef`,
relational comparisons, arithmetic, ternaries, and other general conditional
expressions remain unsupported. Bounded `==` and `!=` comparisons are supported
when both operands are integer or character literals, literal-valued macros, or
`defined(NAME)`; undefined identifiers evaluate to zero.
Canonical whole-header guards (`#ifndef NAME`/`#define NAME`/`#endif`),
`#pragma once`, and the bounded conditional subset are supported. C0 also
supports object-like macros with literal, alias, and multi-token expression
replacements; those macros are expanded in
translation-unit order across a source file and its local headers, and `#undef NAME`
removes one from the active macro state. Backslash-newline splicing precedes
comment handling, including in continued definitions. Expansion is bounded by
depth 64 and one megabyte per expanded line or replacement, plus four megabytes
of cumulative scan work per line. The bounded
conditional subset accepts `#if 0`, `#if 1`, `#if NAME` for a previously defined
0/1 literal macro, `#ifdef NAME`, `#ifndef NAME`, `#if defined(NAME)`,
`#if !defined(NAME)`, and those atoms combined with `!`, `&&`, `||`, or
parentheses. `#elif` with those same conditions, `#else`, and `#endif` are
supported, including nesting; unsupported active conditions receive a
diagnostic.

One- to three-parameter function-like macros are also supported with ordinary
argument substitution, balanced nested calls, and bounded rescanning of
replacements. They are expanded in source order across a source file and its
local headers. Recursive expansion and unsupported parameter features receive
diagnostics.

## Callback contracts have known gaps

A named contract's resource clause cannot read through one of its own
parameters: `views old->left->augmented` guarded by `requires old->left != 0`
fails to prepare, because the clause is lowered with no facts or resources in
scope, so a callback that recomputes from a child link cannot state that
footprint.

## Type support is still narrow

The verifier supports `void` function returns and scalar `int16`, `int32`,
`uint8`, `uint16`, `uint32`, `int64`, and `uint64`, including their standard spellings
(`short`/`int16_t`, `int`/`int32_t`, `unsigned char`/`uint8_t`,
`unsigned short`/`uint16_t`, `unsigned int`/`uint32_t`,
`long`/`long long`/`int64_t`/`ssize_t`, and
`unsigned long`/`unsigned long long`/`uint64_t`/`size_t`), plus the existing
`int32*`, `uint8*`, `int32**`, `uint8**`, and `uint8[]` forms. C typedefs may
alias these modeled types and named struct-pointer types. The 16-bit, `uint32`,
and 64-bit types are not yet available through pointers or arrays. `uint32`
supports modular `+`,
`-`, and `*`, unsigned `/` and `%`, equality, unsigned ordered comparisons,
bitwise operators, and typed shifts; division by zero and invalid shift counts
remain undefined behavior. It does not support `void` objects or
parameters. Scalar casts are supported, with checked narrowing into `int16`,
`uint8`, or `uint16`; pointer and aggregate casts remain unsupported. This is
not a full C integer model: pointer/array forms of `size_t` and the 64-bit
types, plus the complete usual arithmetic-conversion lattice, remain outside
the slice.
Signed `int32` addition, subtraction, multiplication, division, and remainder
are modeled with C undefined behavior for their C undefined cases: overflow,
zero divisors, and `INT_MIN / -1` or `INT_MIN % -1`. `int32` bitwise `&`, `|`,
`^`, unary `~`, `<<`, and `>>` are modeled as fixed 32-bit two's-complement
bitvector operations. C0 models signed `int32 >>` as arithmetic right shift
with sign extension, matching GCC, Clang, and MSVC. Shift counts outside
`0..32`, negative signed left shifts, and unrepresentable signed left-shift
results are undefined behavior.

`int16`, `uint8`, and `uint16` rvalues promote to `int32` for arithmetic, ordered
comparisons, shifts, bitwise operators, assignments, and returns. `uint32` addition and
subtraction are 32-bit modular operations; equality compares the bit patterns,
and ordered comparisons use unsigned order. Assigning or returning an `int32`
into `uint8` is a checked narrowing conversion: the current pure facts must
prove `0 <= value <= 255`. Narrowing to `int16` requires
`-32768 <= value <= 32767`, and narrowing to `uint16` requires
`0 <= value <= 65535`.

The prelude has initial byte-slice and C-string predicates over `uint8[]`, but
there is still no first-class Click string value and no full libc string model.
Pointer/array forms of `size_t` and 64-bit integers, and the full usual
arithmetic conversion story, remain future work.

The first `for` support is sugar over `while`, and its initializer may be a
scalar assignment or scalar declaration initializer. Its step can use scalar
update-statement sugar such as `i++`. Omitted clauses, `continue`, and general
C expression side effects are still unsupported. `i++` is accepted as a
standalone statement, but not as a value-producing expression inside
`j = i++`.

## Aliasing is default

Distinct pointer parameters may alias. Add
`separate(memory(...), memory(...))` whenever a proof depends on non-overlap.

## Requirements cannot freely read memory

Direct memory reads in `requires` propositions are limited. Use a named
predicate for memory-reading preconditions, and unfold it in proof scripts when
the body is needed.

Plain `cstr(p)` introduces an exact spec length, but it does not by itself
produce a structural `loadable` fact. `cstr_readable(p)` is the corresponding
dynamic-loadability relation: it carries an existential length together with
`loadable(p[0..len + 1])` and the prefix/terminator conditions. Unfold it when a
proof needs that witness. `loadable` still covers read safety only; it does not
grant `views` or `owns`, so a later dynamic array read may need a separate
permission/resource fact.

## Guarded memory reads need range forms

Range `.all` and symbolic `.any` lower their bodies under the range-membership
facts, so `p[k]` is memory-safe when the caller has a matching
`loadable(p[lo..hi])`.

Plain logical conjunction does not currently act as a left-to-right guard for
lowering. For example, prefer `(lo..hi).any(|k| { p[k] == x })` over an
explicit `exists (k: int32) { lo <= k and k < hi and p[k] == x }` until the
surface language has a designed guard story for partial C fragments.

## Predicates are opaque

Predicate calls are not unfolded automatically. Exact predicate facts can be
reused, but proving a predicate body or using its consequences generally needs:

<!-- verified-example: mdtests/sorted_pair_unfold_requirement.md -->
```click
unfold(predicate_name);
```

For small concrete bounded `.all` facts, the prover can instantiate the
unfolded forall when proving a matching condition. Larger or more symbolic
range facts may still need more explicit proof support.

## `old(...)` is still a surface construct

`old(...)` is surface syntax for elaborating an expression in the function-entry
context. As an array argument to a pure Click function or predicate, `old(p)`
becomes an entry-state array ref, so `permutation(p, old(p), lo, hi)` has the
expected old-vs-current meaning.

Loop-invariant lowering now applies that same model to old-state pure
functions, so `old(count(p, lo, hi, x))` can elaborate through stdlib `count`
and preserve its `.fold` in Kernel Click. The elaborator still rejects attempts
to capture non-fixed local spec bindings inside `old(...)`.

There is still no public `ref<T>` syntax. Array refs are an internal pure Click
lowering concept for parameters written as `int32 p[]`, `int32* p`,
`uint8 p[]`, or `uint8* p`.

## Existentials need explicit facts

`exists (k: int32) { ... }` is supported, and symbolic `(lo..hi).any(...)`
lowers to a bounded existential. Proof scripts can prove existential goals
with `witness(k = expression);` and can open direct existential preconditions
with `choose(k from requirement N);`. If an explicitly unfolded predicate
requirement lowers to an existential, `choose` can open that requirement too.

The remaining limitations are automation and source selection: `auto` does not
synthesize witnesses, and `choose` currently selects only `requires` clauses by
label or zero-based requirement index. Concrete `.any` ranges still unroll to
finite disjunctions.

## Folds are partly supported

Pure `.fold` supports concrete unrolling and symbolic `RangeFold` terms.
Symbolic folds compare equal modulo accumulator/item binder names. The kernel
knows useful fold facts for current stdlib `count` proofs, but it is not a
general induction engine for arbitrary folds.

Loop invariants now elaborate through spec lowering, so unfolded pure Click
functions can contain `if`, `let`, and `.fold` values over explicit current and
entry memory snapshots. This supports direct invariants such as
`permutation(p, old(p), lo, hi)` when the proof unfolds the relevant predicate.

## Loop invariants need explicit facts

Pointer-writing loops do not implicitly preserve memory. Use invariants,
`owns` clauses, and `separate(memory(...), memory(...))` requirements. Symbolic loops need invariants
for arithmetic bounds, memory safety, and postconditions.

## `simp` is not a solver

`simp` performs deterministic local normalization and selected proof rules. It
does not search broadly, infer missing invariants, synthesize frame conditions,
or invent arithmetic theorems.

## Diagnostics are developer-oriented

Failure messages increasingly expose a proof context split into pure facts and
resource facts, but some lower-level errors still expose internal propositions
and memory terms. They are useful for agents but not yet polished for end
users.
