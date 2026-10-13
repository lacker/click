# Limitations and compatibility

This page lists boundaries that agents should not silently assume away.

## Surface syntax nesting is bounded

Click accepts at most 16 simultaneously nested pairs of parentheses in a
sidecar. Deeper input receives a source-positioned parser diagnostic before
recursive descent begins. This bound covers grouped propositions, grouped
contract expressions, calls, and the other parenthesized surface forms.

Other recursive surface forms have their own bounded budgets: `match`
expressions and conditional contract expressions are limited independently,
while quantifier bodies, proof blocks, and sequence brackets share the
structural nesting budget. These limits likewise fail with a source-positioned
diagnostic before an unbounded recursive parse or AST construction can occur.
Nested algebraic datatype applications and fields use a separate bounded
angle-bracket budget; angle brackets are not included in the general delimiter
preflight because they also spell comparison operators.

The current budgets are 16 for parenthesized and `match` nesting, 32 for the
shared structural and conditional-expression nesting, and 32 for nested
algebraic type applications and fields. Operator chains accept up to 512
operands, unary proposition negation accepts up to 64 prefixes, sequential
contract `let` bindings accept up to 128 bindings, and recursively nested
contract `let` initializers accept up to 8 levels. These are parser/tooling
boundaries, not a promise that every accepted shape is semantically useful:
for example, sequence literals currently require scalar elements, so deeply
nested bracket literals are checked for safe parsing and rendering but are not
valid theorem values.

## Supported C is incomplete

Click does not parse general C. [Language coverage](../coverage.md) summarizes
what supported C admits, beside C++ and Rust, and [Supported C](c.md) defines
the exact forms.

The modeled `malloc`, `calloc`, `realloc`, and `free` forms are listed in
[Heap allocation](c.md#heap-allocation). Compatible
external allocator declarations may describe a supported data-pointer or
pointer-array result with `allocation(result, bytes)` and an owned result
range. Zero sizes, arbitrary byte layouts, `size_t`, allocator results
declared as `void *`, and unrelated custom allocator APIs remain
outside this surface description. Opaque `void *` identity conversions are
supported, but dereference, indexing, arithmetic, and ownership through an
untyped pointer are not.

Plain `char *` and `unsigned char *` remain distinct for implicit conversions
and function signatures. Explicit casts between these one-level byte pointers
are supported and preserve pointer provenance. Casts between `char **` and
`unsigned char **` remain unsupported; sharing byte storage does not make their
pointer cells interchangeable.

Struct support is partial; the [struct subset](c.md#struct-subset) defines
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
in [file-scope objects](c.md#file-scope-scalar-globals) and the struct
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
assumptions used by each verified function. The standard-library `memcpy`
declaration additionally carries a checked representation-copy effect: a copy
that covers the complete representation of an initialized source cell
establishes that cell's value at the mapped destination offset. The effect is
bound to that exact declaration, so a user function named `memcpy` does not
acquire it, and a partial, unaligned, or untyped copy establishes no typed
value. These contracts describe only
supported C types; `void *` dereference or ownership and unbounded string
viewability remain outside the model. `memcpy` requires non-overlapping ranges.

A body-less variadic prototype such as `int report(const char *format, ...);`
is retained as a declaration only. Click has no model of variable arguments,
so calls to such a function, uses of its address, variadic definitions, and
variadic function-pointer signatures are rejected with a located diagnostic;
an `extern` contract does not make the function callable.

A verifying source may contain multiple function definitions and compatible
forward prototypes. Project-local quoted includes such as
`#include "include/types.h"` are resolved relative to the including source when
the named header is supplied in the source bundle. Headers may contain
supported structs, typedefs, enums, prototypes, and `static inline` or
`static __always_inline` function bodies. Those inline bodies are checked from
the expanded translation unit. A call to a helper with a verified sidecar
contract applies that contract as its boundary, like any call; a call to a
helper with no contract executes the checked body directly, on the caller's
own memory and resources. Click never emits a standalone definition or
selects an external one under either supported x86-64 Linux target. Termination follows the same split: a contracted helper is a callee
with its own termination rule, while a contract-less helper is a node of the
caller's call graph, so a straight-line one needs no ranking of its own and a
ranked loop may call it, while one carrying a loop still needs that loop
ranked and a recursive one needs a checked rule for its cycle. `extern inline` has profile-dependent
emission rules and stays rejected, as do bare `inline` and other inline
spellings. The declaration-only GNU spellings
`__attribute__((always_inline))` and `__attribute__((__always_inline__))` are
accepted on those helpers, as is `gnu_inline` on a `static inline` helper
only; other inline attributes and function definitions in headers
remain unsupported. The exact trailing struct spelling
`__attribute__((aligned(sizeof(long))))` (and `__aligned__`) is supported as an
LP64 eight-byte alignment requirement; other alignment forms remain
unsupported. Const-qualified static-storage aggregates are read-only, while
automatic/local const aggregates remain unsupported.
System header includes other than the modeled `<stdint.h>`, `<inttypes.h>`,
`<stdbool.h>`, and `<limits.h>` (and, for the user-space target, `<stddef.h>`,
the declaration-only `<string.h>` and `<stdlib.h>` subsets, `<pthread.h>`, and
the declaration-only `<stdatomic.h>` subset), function-like macros
with more than three parameters, empty arguments, stringification, token pasting,
macro redefinitions without an intervening `#undef`,
relational comparisons, arithmetic, ternaries, and other general conditional
expressions remain unsupported. Bounded `==` and `!=` comparisons are supported
when both operands are integer or character literals, literal-valued macros, or
`defined(NAME)`; undefined identifiers evaluate to zero.
Canonical whole-header guards (`#ifndef NAME`/`#define NAME`/`#endif`),
`#pragma once`, and the bounded conditional subset are supported. Click also
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

## Atomics are one publication protocol

The modeled `<stdatomic.h>` operations cover one protocol: an `atomic_int`
flag initialized to zero publishes one field-less payload once, through a
release store and an acquire load. Other atomic types, read-modify-write
operations, fences, and orders other than release/acquire (including
`memory_order_seq_cst`) are refused. A flag's storage is not returned after
the protocol, and a flag cannot be reinitialized for a second publication.

## Callback contracts have known gaps

A named contract's resource clause cannot read through one of its own
parameters: `views old->left->augmented` guarded by `requires old->left != 0`
fails to prepare, because the clause is lowered with no facts or resources in
scope, so a callback that recomputes from a child link cannot state that
footprint.

## Type support is partial

[Language coverage](../coverage.md#scalar-types) lists the admitted scalar
types, and [Supported C](c.md) gives their spellings and operations. Integer
promotions and the usual arithmetic conversions apply; fully general symbolic
narrowing between unlike 64-bit and narrower integer types does not. A
checked narrowing conversion requires the current pure facts to prove the
value in range. A contract may cast a `void *` parameter to
a struct pointer or convert a current object pointer explicitly through
`void*` to a struct pointer. Other pointer casts, aggregate casts, and `void`
objects or parameters remain unsupported.

Signed `int32` and `int64` addition, subtraction, multiplication, division,
and remainder are modeled with C undefined behavior for their C undefined
cases: overflow, zero divisors, and the minimum value divided by `-1`.
Narrower types promote to `int32` first. `int32` bitwise `&`, `|`,
`^`, unary `~`, `<<`, and `>>` are modeled as fixed 32-bit two's-complement
bitvector operations. Click models signed `int32 >>` as arithmetic right shift
with sign extension, matching GCC, Clang, and MSVC. Shift counts outside
`0..32`, negative signed left shifts, and unrepresentable signed left-shift
results are undefined behavior.

The prelude has initial byte-slice and C-string predicates over `uint8[]`, but
there is still no first-class Click string value and no full libc string model.

## Aliasing is default

Distinct pointer parameters may alias. Add
`separate(memory(...), memory(...))` whenever a proof depends on non-overlap.

## Requirements cannot freely read memory

Direct memory reads in `requires` propositions are limited. Use a named
predicate for memory-reading preconditions, and unfold it in proof scripts when
the body is needed.

Plain `cstr(p)` introduces an exact spec length, but it does not by itself
produce a structural `viewable` fact. `cstr_readable(p)` is the corresponding
dynamic-viewability relation: it carries an existential `size_t` length
together with `viewable(p[0..len + 1u64])` and the prefix/terminator
conditions. Unfold it when a
proof needs that witness. `viewable` still covers read safety only; it does not
grant `views` or `owns`, so a later dynamic array read may need a separate
permission/resource fact.

## Guarded memory reads need range forms

Range `.all` and symbolic `.any` lower their bodies under the range-membership
facts, so `p[k]` is memory-safe when the caller has a matching
`viewable(p[lo..hi])`.

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

`exists (k: int32) { ... }` and multiple-binder forms such as
`exists (x: int32, y: int32) { ... }` are supported. Symbolic
`(lo..hi).any(...)` lowers to a bounded existential. Proof scripts prove an
existential goal with `witness { k: expression };`. To open an already established
existential fact, write `obtain (k: int32) { ... };`; the same form accepts
multiple typed bindings. A predicate requirement can be unfolded first.

`auto` does not synthesize witnesses. `obtain` requires the exact
existential to be available; use `have` to establish it if necessary. Concrete
`.any` ranges still unroll to finite disjunctions.

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

`simp` is a smart tactic: a bounded, deterministic search over the ambient pure
facts and a fixed set of proof rules, including equality rewriting, case splits
on relevant disjunctions, and evidence for supported linear comparisons. A miss
means the search found no proof within its budget, not that the claim is false.

It never executes C, infers missing loop invariants, invents induction, or
solves general nonlinear arithmetic. The [tactics reference](../tactics/index.md)
lists what the search covers.

## Diagnostics are developer-oriented

Failure messages increasingly expose a proof context split into pure facts and
resource facts, but some lower-level errors still expose internal propositions
and memory terms. They are useful for agents but not yet polished for end
users.
