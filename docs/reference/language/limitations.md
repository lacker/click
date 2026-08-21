# Limitations and compatibility

This page lists boundaries that agents should not silently assume away.

## Surface syntax nesting is bounded

Click accepts at most 16 simultaneously nested pairs of parentheses in a
sidecar. Deeper input receives a source-positioned parser diagnostic before
recursive descent begins. This bound covers grouped propositions, grouped
contract expressions, calls, and the other parenthesized surface forms.

## C0 is small

Click does not parse general C. See [Supported C0](c0.md). Missing
features include full structs, unsigned integers beyond the narrow `uint8` byte
type, casts, globals, general allocator compatibility, `switch`, and many
operators.

C0 supports `malloc(sizeof(struct T))` into a matching `struct T*` and
runtime-sized `int32` backing allocations such as `malloc(count * 4)`, with
ordinary null checking and `free`. It does not yet support zero sizes,
arbitrary byte layouts, `size_t`, general `void *` conversions, allocator
declarations, custom allocators, `calloc`, or `realloc`.

Struct support is partial. C0 accepts LP64-layout multi-field struct
declarations with `int32` and pointer-valued fields, plus chained
`p->child->field` loads/stores through struct pointers. It retains pointee
struct names through those chains and models field alignment and tail padding.
It still has no struct values, embedded struct values, arrays of structs,
unions, bitfields, packed layout, or general field-address expressions.
Click contracts can use field places with `views` and the owned-resource verbs,
and explicit ranges such as `owns owner[0..3]` remain useful for broader
footprints. The supported ABI is LP64; other target ABIs are rejected rather
than approximated.

## Type support is still narrow

The verifier supports `void` function returns, `int32`, and a byte-like
`uint8` type, including `uint8*`, `uint8[]`, ASCII character literals, byte
loads/stores, byte promotion through integer operators, and typed Click array
refs. It does not support `void` objects, parameters, or pointers. This is not
a full C integer model: there are no casts beyond checked
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
and bitwise operators. Assigning or returning an `int32` into `uint8` is a
checked narrowing conversion: the current pure facts must prove
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
