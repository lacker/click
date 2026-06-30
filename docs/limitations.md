# Current Limitations

This page lists boundaries that agents should not silently assume away.

## C0 Is Small

Click does not parse general C. See [c0-subset.md](c0-subset.md). Missing
features include full structs, unsigned integers beyond the narrow `uint8` byte
type, casts, globals, heap allocation, `switch`, and many operators.

There is one pilot struct slice for the first real-library fixture: a
single-`int32`-field `struct`, `struct name*` parameters, and `p->field`
loads/stores. Click accepts `valid_field(p->field)` as a field-validity
precondition and `mutable_field(p->field)` as a field-write footprint for that
slice. Field accesses still require the ordinary resource context, such as
`read(p[0..1])` or `write(p[0..1])`, and this is not yet a general layout or
field-frame model.

## Type Support Is Still Narrow

The verifier supports `int32` and a byte-like `uint8` type, including `uint8*`,
`uint8[]`, ASCII character literals, byte loads/stores, byte promotion through
integer operators, and typed Click array refs. This is not a full C integer
model: there are no casts beyond checked `int32`-to-`uint8` narrowing, no broad
usual-arithmetic-conversion lattice, and no general unsigned arithmetic yet.
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
checked narrowing conversion: the current requirements/path facts must prove
`0 <= value <= 255`.

The prelude has initial byte-slice and C-string predicates over `uint8[]`, but
there is still no first-class Click string value and no full libc string model.
Broader casts, additional integer widths, and the full usual arithmetic
conversion story remain future work.

The first `for` support is assignment-style sugar over `while`, and its step
can use scalar update-statement sugar such as `i++`. Declarations in the
initializer, omitted clauses, `continue`, and general C expression side effects
are still unsupported. `i++` is accepted as a standalone statement, but not as a
value-producing expression inside `j = i++`.

## Aliasing Is Default

Distinct pointer parameters may alias. Add `disjoint(...)` whenever a proof
depends on non-overlap.

## Requirements Cannot Freely Read Memory

Direct memory reads in `requires` propositions are limited. Use a named
predicate for memory-reading preconditions, and unfold it in proof scripts when
the body is needed.

Plain `cstr(p)` introduces an exact spec length, but it does not by itself
produce a structural `valid_range` fact. To use byte-level consequences from
`cstr_len` or bounded string facts, the surrounding contract still needs enough
memory-validity information, such as `valid_range(p[0..len + 1])` for an exact
known spec length or `valid_range(p[0..max])` for a bounded scan.

## Guarded Memory Reads Need Range Forms

Range `.all` and symbolic `.any` lower their bodies under the range-membership
facts, so `p[k]` is memory-safe when the caller has a matching
`valid_range(p[lo..hi])`.

Plain logical conjunction does not currently act as a left-to-right guard for
lowering. For example, prefer `(lo..hi).any(|k| { p[k] == x })` over an
explicit `exists (int32 k) { lo <= k and k < hi and p[k] == x }` until the
surface language has a designed guard story for partial C fragments.

## Predicates Are Opaque

Predicate calls are not unfolded automatically. Exact predicate facts can be
reused, but proving a predicate body or using its consequences generally needs:

```click
unfold(predicate_name);
```

For small concrete bounded `.all` facts, the prover can instantiate the
unfolded forall when proving a matching condition. Larger or more symbolic
range facts may still need more explicit proof support.

## `old(...)` Is Still A Surface Construct

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

## Existentials Need Explicit Facts

`exists (int32 k) { ... }` is supported, and symbolic `(lo..hi).any(...)`
lowers to a bounded existential. Proof-step scripts can prove existential goals
with `witness(k = expression);` and can open direct existential preconditions
with `choose(k from requirement N);`. If an explicitly unfolded predicate
requirement lowers to an existential, `choose` can open that requirement too.

The remaining limitations are automation and source selection: `auto` does not
synthesize witnesses, and `choose` currently selects only `requires` clauses by
label or zero-based requirement index. Concrete `.any` ranges still unroll to
finite disjunctions.

## Folds Are Partly Supported

Pure `.fold` supports concrete unrolling and symbolic `RangeFold` terms.
Symbolic folds compare equal modulo accumulator/item binder names. The kernel
knows useful fold facts for current stdlib `count` proofs, but it is not a
general induction engine for arbitrary folds.

Loop invariants now elaborate through spec lowering, so unfolded pure Click
functions can contain `if`, `let`, and `.fold` values over explicit current and
entry memory snapshots. This supports direct invariants such as
`permutation(p, old(p), lo, hi)` when the proof unfolds the relevant predicate.

## Loop Invariants Need Explicit Facts

Pointer-writing loops do not implicitly preserve memory. Use invariants,
`mutable` effects, and `disjoint` requirements. Symbolic loops need invariants
for arithmetic bounds, memory safety, and postconditions.

## `simp` Is Not A Solver

`simp` performs deterministic local normalization and selected proof rules. It
does not search broadly, infer missing invariants, synthesize frame conditions,
or invent arithmetic lemmas.

## Diagnostics Are Developer-Oriented

Failure messages expose internal propositions, path facts, and memory terms.
They are useful for agents but not yet polished for end users.
