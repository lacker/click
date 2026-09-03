# Limitations and compatibility

This page lists boundaries that agents should not silently assume away.

## Surface syntax nesting is bounded

Click accepts at most 16 simultaneously nested pairs of parentheses in a
sidecar. Deeper input receives a source-positioned parser diagnostic before
recursive descent begins. This bound covers grouped propositions, grouped
contract expressions, calls, and the other parenthesized surface forms.

## C0 is small

Click does not parse general C. See [Supported C0](c0.md). Missing
features include broader structs, unsigned integers beyond the narrow `uint8` byte
type, casts, globals, general allocator compatibility, and many operators. The
supported `switch` slice is intentionally narrow: labels must be direct integer
or character literals in one compound body, with no `goto` or arbitrary
constant-expression labels yet.

C0 supports `sizeof` for the modeled scalar and pointer types, plus
`malloc(sizeof(struct T))` into a matching `struct T*` and runtime-sized
`int32` backing allocations such as `malloc(count * sizeof(int32))`, with
ordinary null checking and `free`. The zeroed variants are
`calloc(count, sizeof(int32))` and matching
`calloc(count, sizeof(struct T))` for a `struct T*` target. It does not yet
support zero sizes, arbitrary byte layouts, `size_t`, general `void *`
conversions, allocator declarations, custom allocators, or `realloc`.

Struct support is partial. C0 accepts LP64-layout multi-field struct
declarations with `int32`, `uint8`, named enum fields, fixed one-dimensional
arrays of the supported scalars, and pointer-valued fields, plus chained `p->child->field`
loads/stores through struct pointers. Inline scalar arrays retain their element
width and are accessed through C's array-to-pointer conversion, so
`uint8 buf[16]` uses byte-width indexing rather than pointer-sized storage. It
retains pointee struct names through field chains and models field alignment and
tail padding. Embedded struct fields are aggregate places for nested member
access, so `p->inner.value` lowers to the combined outer and inner offsets
without constructing a runtime struct value. Local arrays of the supported
structs are also accepted for indexed `items[i].field` loads and stores, using
the ABI-sized struct stride.
One-dimensional function parameters declared as arrays of those structs are
supported with the same stride; their declarator length is syntax metadata and
does not change the pointer ABI. Copyable struct values are also supported when
every field is `int32`, `uint8`, a named enum field, or a fixed one-dimensional
array of those scalar elements: parameters, locals, assignments, and returns
use fresh address-backed copies, with enum fields using the same four-byte
scalar representation and array fields copied element by element. Struct
values containing pointers or embedded structs remain unsupported, as do direct
aggregate loads, aggregate resource segments, arrays of embedded structs,
multidimensional inline arrays, bitfields, packed layout, or general
field-address expressions. Named enums use the four-byte scalar ABI
representation; their enumerators are resolved to
int32 values in C expressions, while enum parameters, returns, locals, arrays,
and anonymous declarations remain unsupported. Aggregate fields are not
resource segments; resource clauses must name a leaf field.
Click contracts can use field places with `views` and the owned-resource verbs,
and explicit ranges such as `owns owner[0..3]` remain useful for broader
footprints. The supported ABI is LP64; other target ABIs are rejected rather
than approximated.

## External C functions

Sidecars may declare body-less C callees with `extern` contracts. The kernel
applies those contracts as explicit assumptions, so the callee implementation
is not checked by Click and its preconditions remain caller obligations. The
standard library includes narrow byte-oriented contracts for `memcpy`,
`memcmp`, `memset`, and `strlen`. `click verify` reports the transitive external
assumptions used by each verified function. These contracts still describe
only the supported C0 types; general `void *`, `size_t`, overlap semantics,
and unbounded string loadability remain outside the model.

A verifying source may contain multiple function definitions and compatible
forward prototypes. Project-local quoted includes such as
`#include "include/types.h"` are resolved relative to the including source when
the named header is supplied in the source bundle. Headers are declaration-only
and may contain supported structs, typedefs, enums, and prototypes. System
header includes other than the modeled no-op `<stdint.h>`, arbitrary macros,
conditional compilation, and other preprocessor directives remain unsupported
except for canonical whole-header guards (`#ifndef NAME`/`#define NAME`/`#endif`)
and `#pragma once`.

## Type support is still narrow

The verifier supports `void` function returns, `int32`, and a byte-like
`uint8` type, including their standard spellings (`int`/`int32_t` and
`unsigned char`/`uint8_t`), `int32*`, `uint8*`, `int32**`, `uint8**`, `uint8[]`,
ASCII character literals, byte loads/stores, byte promotion through integer
operators, and typed Click array refs. C typedefs may alias these modeled
types and named struct-pointer types. It does not support `void` objects or
parameters. This is not a full C integer model: there are no casts beyond checked
`int32`-to-`uint8` narrowing, no broad usual-arithmetic-conversion lattice, and
no general unsigned arithmetic yet.
Signed `int32` addition, subtraction, multiplication, division, and remainder
are modeled with C undefined behavior for their C undefined cases: overflow,
zero divisors, and `INT_MIN / -1` or `INT_MIN % -1`. `int32` bitwise `&`, `|`,
`^`, unary `~`, `<<`, and `>>` are modeled as fixed 32-bit two's-complement
bitvector operations. C0 models signed `int32 >>` as arithmetic right shift
with sign extension, matching GCC, Clang, and MSVC. Shift counts outside
`0..32`, negative signed left shifts, and unrepresentable signed left-shift
results are undefined behavior.

`uint8` rvalues promote to `int32` for arithmetic, ordered comparisons, shifts,
and bitwise operators, assignments, and returns. Assigning or returning an
`int32` into `uint8` is a checked narrowing conversion: the current pure facts must prove
`0 <= value <= 255`.

The prelude has initial byte-slice and C-string predicates over `uint8[]`, but
there is still no first-class Click string value and no full libc string model.
Broader casts, additional integer widths, and the full usual arithmetic
conversion story remain future work.

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
produce a structural `loadable` fact. To use byte-level consequences from
`cstr_len` or bounded string facts, the surrounding contract still needs enough
memory-loadability information, such as `loadable(p[0..len + 1])` for an exact
known spec length or `loadable(p[0..max])` for a bounded scan.

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
`mutable` effects, and `separate(memory(...), memory(...))` requirements. Symbolic loops need invariants
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
