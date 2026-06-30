# Click Language

Click files are sidecar specifications for C0 sources.

Terminology:

- **Surface Click** is the user-written `.click` language described here.
- **C fragments** are pieces of C0 syntax inside Surface Click, such as
  `p[k]`, `x + 1`, and `result == n`.
- **Kernel Click** is the explicit proof core produced by elaboration. Users
  normally do not write it directly.

## File Shape

```click
verifying "file.c";

int32 function_name(int32 p[], int32 n) {
    requires n >= 0;
    requires valid_range(p[0..n]);
    ensures label: result == n by auto;
}
```

`verifying "file.c";` names a C source supplied to the verifier. Function
signatures in the `.click` file are checked against the parsed C0 source.

Click signatures currently understand `int32`, `uint8`, `int32*`, `uint8*`,
pilot `struct name*` parameters, and array-parameter spellings such as
`int32 p[]` and `uint8 bytes[]`.
Character literals such as `'x'`, `'\n'`, and `'\0'` are `uint8` values.

Inside C fragments and pure Click expressions over C values, `uint8` rvalues
promote to `int32` for arithmetic, ordered comparisons, shifts, and bitwise
operators. Assigning or returning an `int32` into `uint8` is checked narrowing:
the current requirements/path facts must prove `0 <= value <= 255`.

Each `ensures` clause is a separate guarantee. A guarantee may be labeled with
`label:`. Omitting a proof clause uses the default prover, currently `auto`.

## Requirements

Requirements are shared by all guarantees for the function.

Supported structural requirements:

```click
requires input_nonnegative: n >= 0;
requires valid_range(p, 12);
requires valid_range(p[0..n]);
requires valid_range((p + 1)[0..1]);
requires disjoint(dst[0..n], src[0..n]);
requires read(p[0..1]);
requires write(p[0..1]);
```

Requirement labels use the same `label:` spelling as `ensures` labels. Labels
are optional, but they are the preferred way for proof-step scripts to refer to a
specific precondition, for example `choose(k from requirement has_k);`.

`valid_range(base[start..end])` and `disjoint(left[start..end],
right[start..end])` use half-open `int32` element ranges. The byte count is
derived from the base pointer's element type: four bytes for `int32[]`, one
byte for `uint8[]`. This `..` syntax is Click contract syntax, not C
fragment syntax.

`requires` can also use Click propositions, but direct memory reads in
requirements are intentionally limited. If a precondition needs memory reads,
package it as a named predicate and unfold it at proof sites when needed.

## Read, Write, And Free Resources

`read(base[start..end])`, `write(base[start..end])`, and
`free(base[start..end])` are the first resource-context permissions. They are
not classical predicates: they are carried in the verifier's resource context
rather than copied as ordinary proof facts.

```click
int32 write_next(int32 p[], int32 x) {
    requires write(p[0..1]);
    requires x < 2147483647;

    ensures p[0] == x + 1 by auto;
    ensures write(p[0..1]) by auto;
}
```

Permission checking is mandatory for external memory. External loads require
covering `read(...)` or `write(...)`, and external stores require covering
`write(...)`. Resource ranges use the element width of the pointer expression,
so `int32 p[]` ranges count four-byte cells and `uint8 bytes[]` ranges count
bytes. Local stack accesses do not require resources. A function with no
resource context has no permission to access external memory.
In practice, top-level verification gets a resource context from
`requires read(...)`, `requires write(...)`, and `requires free(...)` clauses,
while function calls use the callee's resource summary.

`write(...)` implies `read(...)`: a write resource permits both loads and
stores, and can satisfy an `ensures read(...)` guarantee. `read(...)` is
copyable across calls. A callee can declare `requires read(...)` without
consuming the caller's read or write permission. `write(...)` is transferred
linearly: a callee must declare `requires write(...)` to receive write
permission and `ensures write(...)` to return it. `free(...)` is also linear,
does not grant read or write access, and consuming it removes overlapping access
resources from the caller context.

A call can pass a covered subrange, such as passing `write(p[0..1])` from a
caller that has `write(p[0..2])`; Click keeps the residue and rejoins adjacent
returned ranges. The same applies to symbolic ranges when the current facts
prove the subrange is covered. In this first slice, `write(...)` also seeds the
matching symbolic memory cells for concrete `int32[]` ranges, so simple
one-cell int32 writes do not need a separate `valid_range(...)` requirement.
`read(...)` does not seed memory cells; validity remains separate from
permission.

This is intentionally not the full permission system. There are no fractions,
ownership predicates, explicit resource algebra proof steps, C heap allocation,
or executable `free(p)` semantics yet. `valid_range`, `mutable`, and
`immutable` remain separate from permission: validity proves an access is in
bounds, while resources authorize the access.

## Propositions

Click proposition connectives are words:

```click
result == x and not (result != x)
result == x implies result >= 0
forall (int32 k) { 0 <= k and k < n implies p[k] == old(p[k]) }
exists (int32 k) { 0 <= k and k < n and p[k] == x }
```

Do not use C logical operators such as `&&`, `||`, or `!` in Click
propositions. Those remain C-fragment syntax.

Range proposition helpers:

```click
(lo..hi).all(|k| { p[k] <= x })
(0..3).any(|k| { p[k] == x })
```

`.all` lowers to a guarded bounded universal proposition. `.any` lowers to a
bounded existential proposition when its bounds are symbolic; concrete `.any`
ranges still unroll to a finite disjunction. While lowering the range body, the
elaborator assumes the item is inside the range, so bodies such as `p[k] == x`
can use `valid_range(p[lo..hi])` for memory safety.

Prefer these range combinators for guarded memory reads. A plain proposition
such as `exists (int32 k) { lo <= k and k < hi and p[k] == x }` does not
currently let the earlier conjunct guard the later memory read during lowering.

Existential goals are proved explicitly in proof-step scripts with `witness`.
The witness name must match the existential binder. For a symbolic `.any`, the
range item name is the existential binder:

```click
ensures found: (lo..hi).any(|k| { p[k] == result }) by {
    symbolic_execute();
    witness(k = lo);
    simp();
    close();
}
```

## `old(...)`

`old(expression)` evaluates a contract expression in the function-entry state.
It is mainly used in postconditions and invariants:

```click
ensures p[0] == old(p[0]) by auto;
ensures forall (int32 k) { 0 <= k and k < n implies p[k] == old(p[k]) } by auto;
```

Inside `old(...)`, `result` is unavailable.

When `old(p)` is passed as an array argument to a pure Click function or
predicate, it becomes an entry-state Click array ref. For example,
`permutation(p, old(p), 0, 2)` compares post-state `p` to entry-state `p`.
See [click-core.md](click-core.md).

## `at(...)`

`at(selector, expression)` evaluates a contract expression at a selected visit
to a program point. The initial supported selectors are deliberately narrow:

```click
at(function.entry, x)
at(loop_label.entry, x)
```

`at(function.entry, expression)` is equivalent to `old(expression)`.

`at(loop_label.entry, expression)` is currently supported inside invariants for
that same labeled loop code region. It evaluates `expression` at the visit just
before the loop region starts, then reuses that snapshot for invariant entry and
preservation checks.

## Pure Click Functions

Click functions are specification-level value definitions, not executable C
functions.

```click
function inc(int32 x) -> int32 {
    x + 1
}

function eq_as_int(int32 x, int32 y) -> int32 {
    if x == y { 1 } else { 0 }
}

function count3(int32 p[], int32 x) -> int32 {
    let initial: int32 = 0;
    (0..3).fold(initial, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

Supported expression features include parameters, literals, `+`, `-`, `*`,
`/`, `%`, `<<`, `>>`, `int32` bitwise `&`, `|`, `^`, unary `~`, indexing,
`let name [: type] = value; body`, `if proposition { then } else { else }`,
range `.fold`, and calls to other non-recursive Click functions. Recursive
Click functions are rejected.

Function contracts may also use contract-level `let` bindings:

```click
int32 bounded_increment(int32 x) {
    let max: int32 = 2147483647;
    let expected = x + 1;

    requires x < max;
    ensures result == expected by auto;
}
```

Contract-level lets are immutable lexical abbreviations. They are visible to
later clauses in the same function block, including `requires`, `ensures`,
`mutable`, and structural proof blocks. A contract-level let cannot reuse a C
parameter name or an earlier contract-level let name. Explicit type annotations
are checked when the binding is evaluated.

Proposition clauses may also use witness lets:

```click
let k: int32 where k == x;

ensures result == k by {
    symbolic_execute();
    witness(k = x);
    simp();
    close();
}
```

`let name: type where proposition; body` means `exists (type name) {
proposition and body }`. Contract-level `let ... where` applies that shape to
each later proposition clause. The type annotation is required. The current
implementation supports this in proposition clauses; it is intentionally
rejected in `valid_range`, `mutable`, and other memory-segment expressions
until Click has a contract-wide witness environment.

In pure Click function parameters, `int32 p[]` and `int32* p` are treated as
array-ref parameters. `uint8 p[]` and `uint8* p` are also array-ref parameters,
with one-byte indexing and `uint8` loads. Indexing `p[k]` loads from the memory
snapshot carried by that argument. This is why `count(p, ...)` can be called
with either current `p` or `old(p)`.

Click array refs carry their element type. Passing an `int32[]` ref to a pure
Click function or predicate parameter declared as `uint8[]` is rejected.
The same typed array-ref model is used by loop-invariant spec lowering, so a
pure helper over `uint8[]` can appear in an invariant or inside `old(...)`.

The prelude currently provides byte-slice helpers over `uint8[]`: `byte_count`,
`bytes_equal`, `bytes_equal_range`, `bytes_all_eq`, `bytes_contains`, and
`bytes_all_not_eq`. It also provides first-pass C-string predicates:
`cstr_prefix`, `cstr_len`, `cstr`, and `cstr_bounded`. These are ordinary Click
functions and predicates, not built-in kernel concepts.

The first pilot struct slice accepts `obj->field` as a current-state C fragment
for a single-`int32`-field struct, and C0 can write that field. `requires
valid_field(obj->field);` is the matching field-validity precondition and
currently lowers to four bytes at the start of the object. `mutable_field`
accepts the same field-access shape for field writes and lowers to the
one-element mutable segment at the start of the object. This is not yet a
general struct expression, layout, or field-frame model.

Concrete folds are unrolled. Symbolic folds remain `RangeFold` value terms in
the kernel and can be reasoned about by supported fold laws.

## Predicates

Predicates return Click propositions:

```click
predicate sorted_range(int32 p[], int32 lo, int32 hi) {
    forall (int32 i) {
        forall (int32 j) {
            lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}
```

Predicate calls are opaque by default. Requirements and loop invariants can
reuse exact predicate facts, but Click does not unfold predicate bodies unless a
proof asks for it:

```click
ensures sorted: sorted_range(p, 0, n) by {
    symbolic_execute();
    unfold(sorted_range);
    simp();
    close();
}
```

In loop invariants, an unfold-only proof block exposes predicate bodies before
the loop verification condition is generated.

Like pure Click functions, predicate array parameters are Click array refs.
A predicate can compare two arrays from different memory states when its caller
passes arguments such as `p` and `old(p)`.

## Effects

Function-level effects are separate from postconditions:

```click
immutable by frame;
mutable p[0..n] by frame;
mutable dst[0..n], counter[0..1] by frame;
```

`immutable` proves there are no externally visible memory writes. `mutable`
states an upper bound on externally visible writes. It does not claim every
listed cell changes.

Loop-level and step-level effects are described in [proof-workflow.md](proof-workflow.md)
and [memory-model.md](memory-model.md).
