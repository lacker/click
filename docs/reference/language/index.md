# Click language reference

This page is the complete reference for Surface Click, the language of `.click`
sidecar files. Click files are sidecar specifications for C, C++ and Rust
sources.

They may begin with local specification imports such as
`import "../models/common.click";`, and Click library imports such as
`import click::c::string;`. Imports contribute declarations but do not select the
imported file's theorem, C function, or tactic proofs. See
[Files and sidecars](../../concepts/sidecars.md#local-specification-imports)
for the module and selection rules.

Terminology:

- **Surface Click** is the user-written `.click` language described here.
- **C fragments** are pieces of C syntax inside Surface Click, such as
  `p[k]`, `x + 1`, and `result == n`.
- **Kernel Click** is the internal, typed proof core produced by elaboration.
  It has no `.click` concrete syntax and is never emitted as proof text.

Surface Click is closed under expansion: every expression printed by
`click-expand`, the profiler, or a diagnostic is ordinary documented `.click`
syntax accepted by the same parser. Generated text is not a private dialect.

## Core forms

The forms most sidecars use, with the section that defines each. The rest of
this page covers each form's full rules and edge cases.

| Form | Meaning | Section |
| --- | --- | --- |
| `verifying "file.c";` | Names the C source the sidecar's contracts describe | [File shape](#file-shape) |
| `int32 f(int32 x) { requires P; ensures Q; }` | A C function's contract; an omitted proof runs the C and closes each claim | [File shape](#file-shape), [Requirements](#requirements) |
| `} by { step(); close(); }` | An explicit proof script for the contract | [Tactics](../tactics/index.md) |
| `views p[0..n];`, `owns p[0..n];` | Read and write resources a call needs and keeps | [Read and write resources](#read-and-write-resources) |
| `decreases e;` | Termination measure of a recursive function or a loop | [C termination](#c-termination) |
| `old(e)`, `at(region(N).entry, e)` | A value in the entry state or another recorded state | [`old(...)`](#old), [`at(...)`](#at) |
| `exact(p[i])` | A read named by the state in scope itself, not its cell's version point | [`exact(...)`](#exact) |
| `P and Q`, `P or Q`, `P implies Q`, `not P` | Proposition connectives (C's `&&` and `\|\|` are not Click syntax) | [Propositions](#propositions) |
| `forall (k: int32) { P }`, `(lo..hi).all(\|k\| { P })` | Quantified propositions; the range form guards memory reads | [Propositions](#propositions) |
| `Integer`, `to_integer(x)` | Unbounded mathematical integers | [Mathematical integers](#mathematical-integers) |
| `true`, `false`, `-> Bool`, `ensures p(x);` | The logical sort `Bool`; a `Bool` value written alone is the claim that it holds | [Booleans](#booleans) |
| `Pointer`, `load<Pointer>(a)`, `p as Pointer` | Click's untyped pointer: an address and a provenance with no pointee type | [Untyped pointers](#untyped-pointers) |
| `function f(x: int32) -> int32 { ... }` | A pure Click function | [Pure Click functions](#pure-click-functions) |
| `predicate p(...) { ... }` | A named proposition, possibly over resources | [Predicates](#predicates) |
| `theorem t() { requires P; ensures Q; }` | A pure theorem | [Pure theorems](#pure-theorems) |
| `extern int32 g(int32 x) { ... }` | A contract for a C function outside the verified sources | [External function contracts](c.md#external-function-contracts) |
| `tactic name(...) { ... }` | A user-defined tactic | [User-defined tactics](#user-defined-tactics) |

## Contract declarations

A contract is a function declaration written as the verified source's language
writes it, followed by a clause block. A prefix says what it declares:

| Prefix | Declares | Proof |
| --- | --- | --- |
| none | a function in the verified sources | `by ...`, or omitted |
| `extern` | a function outside the verified sources, trusted | none allowed |
| `contract` | a named function type, an interface, not a function | none allowed |

The head has exactly the declaration's types, checked against the source
(`long` is not `long long`); the clauses use Click's types and names in every
language. A `contract` names the type a callback parameter's contract has,
`requires Doubling(f);`, and a function value meets it from its own contract
or by a refinement theorem. In C, the head is a C declaration:

<!-- verified-example: mdtests/c_named_function_contract_refinement_theorem.md -->
```click
contract void MakePositive(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] > 0;
}
```

In C++, the head is a C++ declaration, with qualified members, implicit
`this` and references:

<!-- verified-example: mdtests/cpp_lambda_named_contract.md -->
```click
contract int Doubling(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int apply(int (*f)(int), int x) {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
```

In Rust, it is a Rust item, with module paths and `impl` blocks. A
refinement theorem names a crate function as a value by its path, as Rust
passes it, where C writes `&f`:

<!-- verified-example: tests/fixtures/rust-verification/contract_declarations.click -->
```click
verifying "callback.rs";

contract fn Doubling(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

fn function_pointers::twice(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

fn function_pointers::apply(f: fn(i32) -> i32, x: i32) -> i32 {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

theorem twice_is_doubling() {
    ensures Doubling(function_pointers::twice) by {
        unfold(Doubling(function_pointers::twice));
        close();
    }
}

fn function_pointers::caller(x: i32) -> i32 {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { apply(twice_is_doubling()); }
```

An `extern` head is written the same way in each language:
`extern int32 g(int32 x)` in C (`mdtests/external_function_contract_call.md`),
`extern int ministd::Box::get() const` in C++
(`tests/cpp_import.rs::axiomatic_member_function_extern_heads_are_cpp_declarations`),
and `fn extern_functions::clamp_reading(raw: i32) -> i32` in a Rust interface
([`design/charon-trial/extern-functions`](https://github.com/clicklang/click/blob/master/design/charon-trial/extern-functions/ffi.interface.click)).
The Rust syntax is in [the Rust reference](../rust.md), the C syntax in
[C](c.md).

## File shape

<!-- verified-example: mdtests/click_file_shape.md -->
```click
verifying "file.c";

int32 function_name(int32 p[], int32 n) {
    requires n >= 0;
    requires viewable(p[0..n]);
    ensures label: result == n;
}
```

`verifying "file.c";` names a C source supplied to the verifier. Function
signatures in the `.click` file are checked against the parsed C source.
Those attached signatures deliberately retain C declaration order. Typed
binders introduced by Click itself use `name: type`: theorem and resource
parameters, pure-function and predicate parameters, typed `let` bindings, and
`forall`/`exists` variables.

### Signature types

A signature uses the C types Click models, by their C names (`int`,
`unsigned char`, `size_t`, `int32_t`, ...) or Click's own names (`int8`,
`uint16`, `int32`, `uint64`, ...), with pointers, `struct name*` parameters,
and array-parameter forms such as `int32 p[]` and `uint8 bytes[]`; the
complete list is [Supported C](c.md). C typedefs may alias these modeled
types. `void` is not an object or parameter type. A `void` contract has
no `result` binding; it may still state resource transfer and return-state
propositions that do not mention a result.
Unsigned `uint32` literals retain their nonnegative decimal value and `u32`
suffix in failed claim labels, including values at and above `2147483648u32`;
see [`failed_uint32_claim_preserves_the_high_bit.md`](https://github.com/clicklang/click/blob/master/mdtests/failed_uint32_claim_preserves_the_high_bit.md).

Character literals such as `'x'`, `'\n'`, and `'\0'` are `uint8` values.

Inside C fragments and pure Click expressions over C values, `uint8` rvalues
promote to `int32` for arithmetic, ordered comparisons, shifts, and bitwise
operators, assignments, and returns. `uint32` addition, subtraction, and
multiplication wrap at 2^32; division and remainder use unsigned arithmetic,
bitwise operators use the raw 32-bit pattern, and right shifts are logical.
Equality compares the bit pattern and ordered comparisons use unsigned order.
Closed unsigned left shifts also evaluate after rewriting their shift count
through casts, unsigned subtraction, and a bitwise mask. Raw 32-bit shift
terms fold their bit pattern; signed C overflow and counts outside `0..31`
remain separate checked obligations. Residual theorem goals retain machine
parameter types in diagnostics. See
[`uint32_shift_by_a_folded_mask.md`](https://github.com/clicklang/click/blob/master/mdtests/uint32_shift_by_a_folded_mask.md)
and its negative and unsigned residual companions.
Assigning
or returning an `int32` into `uint8` is checked narrowing: the current pure
facts must prove `0 <= value <= 255`.

### Implicit conversions

In Click syntax a value converts implicitly to another type only when the
conversion is exact: every value of its type is a value of the other. An
`int32` converts to `int64`, a `uint32` to `int64`, a `uint8` to `uint32`,
and an `int32` to `double`. A conversion that can change a value, a
narrowing such as `int64` to `int32`, a change of sign such as `int32` to
`uint32`, or a float's integer part, is written, as a cast `e as int32` or a
checked `to_int32(e)`. An integer literal converts to any integer type that
holds its value and is refused where it does not. C source keeps C's own
conversions, including its modular ones; this rule is for Click's typed
positions.

A constructor's field takes its argument by this rule: `Seq<int64>::Cons(x,
Seq<int64>::Nil)` with `x: int32` holds `x` widened to `int64`, and
`Seq<int32>::Cons(y, ...)` with `y: int64` is refused until the narrowing
is written. A constructor whose type arguments are left to inference takes
them from the type its position expects, a function's return type or a
`let`'s written type, before its own arguments, so
`function wrap(x: int32) -> Seq<int64> { Seq::Cons(x, Seq::Nil) }` builds
a `Seq<int64>`. A pure function's or predicate's argument and a pure
function's result follow the same rule: `byte_plus_one(256)` with a `uint8`
parameter is refused, and `byte_plus_one(256 as uint8)` passes `0`. The
`bytes::` predicates measure ranges in `size_t`, so a C `int32` length is
passed as `n as uint64`.

### Casts

A cast is written after its operand, `e as T`. A numeric target is bare:
`x as uint32`, `old(x) as int32`, `n / d as int128`, `x as float`, `x as double`. A pointer target is
parenthesized: `p as (uint8 *)`, `p as (void *)`, `p as (struct node *)`,
`p as (const struct node *)`. The targets are the ten machine integer types
`int8` to `uint128`, `float`, `double`, `void *`, a pointer to one of them,
a pointer to a struct, and Click's untyped pointer, bare like a numeric
target: `p as Pointer` ([Untyped pointers](#untyped-pointers)). Native pointer targets may add `const`, `volatile`,
or both before the pointee type, such as `p as (const uint8 *)`; struct pointer
targets support `const`. An unqualified byte view inherits its source's const
qualification. Casting a pointer from a non-character type, including
`void *`, to a byte pointer forms the byte view of its allocation, as the C
conversion does; casting to `void *` or between byte pointer types keeps the
pointer's bounds. Qualifying a pointer grants no
memory access permission. A `void *` has no pointee type, as in C, so
`*q` and `q[i]` on one are refused ("a `void *` has no pointee type; cast
it to a typed pointer or use `load<T>`"); a spec casts first,
`*(q as (uint8 *))`, or reads `load<T>(q)`
(`mdtests/void_pointer_spec_dereference_is_refused.md`); a call's `void *`
result is refused the same way, so `statement(0).call(get, 0).result[0]`
needs a cast (`mdtests/void_pointer_call_result_index_is_refused.md`).
`q + k`, `k + q` and `q - k` step a `void *` by `k` bytes, as Click's C
side does (the GNU extension), so `ensures result == q + 1` states a body's `return q + 1;`
(`mdtests/void_pointer_spec_addition_steps_one_byte.md`,
`mdtests/void_pointer_spec_step_reads_the_next_byte.md`); the difference of
two `void *` is refused
(`mdtests/void_pointer_spec_difference_is_refused.md`). A range
`q[a..b]` in `views` or `owns` counts elements, so one based at a `void *` is
refused; `(q as (uint8 *))[0..n]` states the bytes
(`mdtests/void_pointer_range_is_refused.md`). A Rust source's sidecar
also writes Rust's scalar names, `x as u32`.

Float pointer casts preserve the address and use the existing pointer-cast
rules: in a pure-function body, a non-byte scalar pointer target requires a
`void *` source. A byte pointer therefore uses
`p as (void *) as (float *)` (or `double *`). Reads and arithmetic after
`p as (float *)` or `p as (double *)` use that pointee's width. A cast supplies no access permission or initializedness,
and does not perform a numeric conversion of the stored bits.
See `mdtests/contract_float_pointer_casts.md` for reads and pointer strides.

The numeric targets `float` and `double` use the existing C binary32 and
binary64 conversion rules, including integer rounding, width conversion,
signed zero, infinities, and NaNs. Like integer targets, these Click forms
cast the value observed by their operand, including `old(...)` and `at(...)`.
They do not add a conversion from mathematical `Integer` or 128-bit integers.
Float-to-integer casts require ordered bounds on the range after truncation.
Together these bounds exclude NaN and infinities. Checked
examples: `mdtests/float_numeric_cast_spellings.md`.

`as` binds tighter than every binary operator and looser than every unary
one, as in Rust, and chains left to right:

| Written | Reads |
|---|---|
| `x as int32 + 1` | `(x as int32) + 1` |
| `-x as int32` | `(-x) as int32` |
| `-(x as int32)` | the negation of the cast |
| `*(p as (uint8 *))` | a read through the byte view |
| `x as int32 as uint64` | `(x as int32) as uint64` |
| `(a + b) as uint32` | the cast of the sum |

The C form `(T) e` is refused in Click text, with the suggestion to write
`e as T` (`e as (T *)` for a pointer); C source keeps C's casts. A name bound by
`let ih = induct(x)`, `let n = intro()`, `verifying "f.c" as
f` or a loop label, may not be a cast's type name. Diagnostics, expansions
and synthesized proofs print casts in this form, parenthesized only where
precedence requires (`design/machine-integers.md`, Decisions, 2026-10-26). The
precedence and the refusals are checked by
`mdtests/a_cast_binds_tighter_than_binary_operators.md`,
`mdtests/a_c_style_cast_in_click_text_names_the_as_form.md`,
`mdtests/an_integer_cast_target_is_written_without_parentheses.md` and
`mdtests/a_binder_named_like_a_type_is_refused_beside_as.md`.

### Postconditions

Each `ensures` clause is a separate guarantee. A guarantee may be labeled with
`label:`. An omitted proof clause is the implicit tail alone: it runs the C to
function exit and closes the claim on every path.

An `ensures` clause describes every return state, and a C contract also
asserts that a return state exists: every verified C function returns unless
its signature says `diverges`. See [C termination](#c-termination). Checked
undefined behavior, resource authority, and declared write footprints remain
safety properties of every finite execution prefix, including prefixes of an
execution that never returns, which is what a `diverges` contract keeps.

### Exceptional results

A function may declare one checked exceptional result channel by placing
`throws int32` after its parameter list. Its `exceptional ensures` clauses are
a separate postcondition family, and the thrown payload is named `exception`:

<!-- verified-example: mdtests/exceptional_contracts.md -->
```click
int32 identity(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

Ordinary `ensures` is owed only by normal returns and may use `result`;
`exceptional ensures` is owed only by throws and may use `exception`. Neither
payload name is available in the opposite family. Omitting `throws`
declares a nonthrowing interface.

A direct throwing contract may borrow memory with `owns` and `views`.
Those permissions hold on both exits; `exceptional ensures` may describe
changed memory and use `old(...)`. `consumes`, `produces`, `constructs`,
conditional resource clauses and nonmemory resources remain refused with
`throws`. Normal guarantees never become exceptional guarantees.

The C++ `ios_failure` import profile also supports
`throws std::ios_base::failure`: `exception` is an opaque value of exactly
that type, with no addressable layout, message or `what()` accessor
([import boundary](../cli/capture.md)).

For ordinary imported C++ aggregates, the `typed` profile permits
`throws Error` or `throws errors::ParseError`. The name resolves to an
imported class; two classes with the same fields remain distinct exception
types. The payload is opaque, so `exception.code` is refused. Initializers in
`throw Error{expression}` are checked normally; opaque payloads do not hide
invalid reads or arithmetic overflow. Empty tag classes are supported too.

Throwing named callback contracts remain pure and accept only `throws int32`.
An `extern` declaration may carry the same direct throwing interface. A call
through a pointer under a throwing contract, or to a throwing `extern`, has
both outcomes, as a direct call
does. Whether a function may throw is part of its contract, not of its
pointer type: a function that never throws meets a contract that may, a
function that may throw meets only a contract that may, and its
`exceptional ensures` must give the contract's
(`mdtests/exceptional_named_contract.md`,
`mdtests/exceptional_external_contract.md`). An explicit refinement theorem
for a source that may throw reports `unsupported`. The automatic refinement
check handles throwing contracts. Explicit refinement would need to generate
and check each exceptional postcondition implication alongside the normal
one. The separate C++ scalar-exception import profile accepts typed `throw int32`, one typed `try`/`catch (int name)`
with a fresh payload binding, and the narrow single-guard cleanup shape
documented by the import reference. It still rejects nested handlers and other
catch forms. A direct modular call whose normal
continuation is a single return can certify both caller outcome families:

<!-- verified-example: mdtests/exceptional_terminal_call.md -->
```click
int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

A checked call-outcome fork also lets the normal successor continue through
later scalar assignments and C branches while retaining the call's separate
exceptional exit. No new Click tactic is needed:

<!-- verified-example: mdtests/exceptional_call_continuation.md -->
```click
int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

The scalar C++ profile can turn a caught `int32` exception into a normal
return without a `throws` declaration on the catching function. This does not
model general object unwinding or consuming/producing exceptional resource transitions.

### Recursion

C functions may call themselves or participate in mutual recursion without a
special Click keyword. Their ordinary contracts are the modular interfaces for
recursive calls. Click checks all functions in the selected call-graph
transaction before returning any verified rules, so declaration order does not
control whether a callee contract is available. A recursive component is a
real cycle, so it carries a function-level `decreases` measure of its own; see
[C termination](#c-termination). Recursive pure Click functions carry the same
obligation for a different reason, and cannot waive it: a pure call must
produce a value, so there is no `diverges` marker for one.

### C termination

Every verified C function must have termination evidence for every reachable
loop, every recursive cycle, and every callee. Write `decreases` wherever
there is a real cycle that Click does not already rank: a loop the proof
summarizes, or a recursive call. A `decreases` clause is always one expression, and what it names
decides which measure it is: an `int32` parameter, a resource application such
as `list(node)`, a contract or loop resource binder such as `t`, or, on a
self-recursive function, any pure `int32`, unsigned, or mathematical
`Integer` expression, or a parenthesized lexicographic tuple of them. Functions
and resources share one namespace, so that classification happens after name
resolution rather than from a keyword; there is no `decreases resource`
form. Measure arithmetic is exact Integer arithmetic: `decreases a + b;`
ranks by `to_integer(a) + to_integer(b)` without a machine-overflow obligation.
A function-level measure ranks recursive calls:

<!-- verified-example: mdtests/c_decreases_recursive.md -->
```click
int32 countdown(int32 n) {
    decreases n;
    ensures result == 0;
}
```

A loop measure belongs to the loop handled at the current execution frontier:

<!-- verified-example: mdtests/c_decreases_loop.md -->
```click
by {
  loop {
    decreases n;
    invariant n >= 0;
  }
}
```

That frontier may be one a `branch` arm or a proof-level `if` arm reached, so a
loop guarded by a C `if` declares its measure inside that arm. Termination is
judged from the rule the arm constructed, and an arm that omits `decreases` is
refused like any other unranked loop (`mdtests/loop_inside_a_branch_arm.md`).

Recursive traversal of an inductive resource may instead use its hidden
structural rank:

<!-- verified-example: mdtests/c_decreases_resource_mutating_nullable.md -->
```click
void list_destroy(struct node* node) {
    decreases allocated_list(node);
    consumes allocated_list(node);
}
```

The measure may name a field, `decreases nodes(self->next)`: the field's
narrowing changes neither what the guard tests nor which child a call passes
(`mdtests/c_decreases_resource_field_measure.md`).

A self-recursive function may instead rank itself by any pure `int32`
expression: a C fragment, a memory read, an application of a pure Click
function, a resource model field — the same vocabulary a loop component has.
This is what ranks a recursion whose real measure has no parameter to name,
such as one that walks a cell the same pointer keeps pointing at:

<!-- verified-example: mdtests/c_decreases_memory_measure_recursion.md -->
```click
int32 drain(int32 box[4]) {
    decreases head(box);
    owns box[0..4];
    requires box[0] >= 0;
    ensures result == 0;
}
```

Every numeric measure, including a bare parameter such as `decreases n`,
creates ordinary call obligations rather than requesting an analysis of the
body. Click reads the declared expression once at the function's own entry,
giving the value M0 the recursion
starts from, and again at each call to that function inside it, at the state
the callee's preconditions are read at. The call then owes two ordinary
verification conditions, which the proof discharges before its `step()`, just
as it discharges a precondition:

* the measure at the call is nonnegative, and
* the measure at the call is strictly below M0.

The application stays opaque, so each obligation is stated with a `have` that
unfolds it, and `old(...)` names the entry reading — the function-level
counterpart of the `invariant head(box) == box[0]` idiom a loop uses. See
`mdtests/c_decreases_pure_expression_recursion.md` and
`mdtests/c_decreases_memory_measure_recursion.md`. A measure the recursive
call does not lower leaves the descent obligation open exactly as a loop's
does: `mdtests/c_decreases_pure_expression_recursion_must_descend.md`.

The measure may instead be `Integer`-valued, and then the two members are
Integer comparisons. A counting measure is naturally a mathematical `Integer`:
an int32 fold's `+` is partial in specifications, so its bounds are unprovable
at a symbolic length. `<` on the nonnegative Integers is well founded for the
same reason `<` on the nonnegative int32s is, so nothing about the argument
changes — only the carrier the two obligations are stated in. The
`click::integer` library module's
`integer::int32_less_equal_to_integer` and `integer::int32_subtract_to_integer` carry the int32
the C counts into the Integer the measure names. See
`mdtests/c_decreases_integer_measure_recursion.md`.

A bare parameter of another numeric type uses the same call obligations:
`decreases b` on a `uint32` parameter is ranked by the descent obligations
above. Euclid's `gcd(b, a % b)` discharges `a % b < b` with
`click::integer`'s `integer::uint32_remainder_less_than_divisor`
(`mdtests/c_decreases_unsigned_parameter_recursion.md`, and the negative
`mdtests/c_decreases_unsigned_parameter_recursion_must_descend.md`).

A self-recursive function may also declare a lexicographic tuple, with the
loop slot's syntax and rule. Each call owes every component nonnegative, and
some component strictly below its entry reading with every earlier component
unchanged. Ackermann's function is ranked by `(m, n)`:

<!-- verified-example: mdtests/c_decreases_lexicographic_recursion.md -->
```click
int32 ack(int32 m, int32 n) {
    decreases (m, n);
    requires m >= 0;
    requires n >= 0;
    ensures result >= 0;
}
```

The order of the components is part of the measure
(`mdtests/c_decreases_lexicographic_recursion_rejects_swapped_order.md`), and
a later component must stay nonnegative even when an earlier one decreases
(`mdtests/c_decreases_lexicographic_recursion_rejects_negative_component.md`).

The same rule about fixed states applies: a function-level component may not
mention `old(...)` or `at(...)`, because Click reads each declared component
at two states itself.

A self-call inside a summarized loop owes the same two obligations. A loop is
verified as its own judgment, so the descent there is owed by the loop's proof
rather than by a step of the function's, and Click certifies every loop of a
function that declares a measure under that function's anchor: the call in the
body raises the same members, against the same function-entry M0. Loop phases
read `old(...)` at the function entry too, so `old(...)` names M0 inside a
`maintain by { ... }` exactly as it does in the contract proof, and what
relates the iteration's state to the entry is an invariant the user writes,
such as `invariant n <= old(n)`. See
`mdtests/c_decreases_pure_expression_recursion_in_loop.md`,
`mdtests/c_decreases_pure_expression_recursion_in_havocked_loop.md`, and the
negative `mdtests/c_decreases_pure_expression_recursion_in_loop_must_descend.md`.
A loop whose verified rule was certified without the anchor is refused by
name rather than summarized past: the summary would answer for a call that
owed nothing.

An expression measure also ranks a **mutually recursive component**. Every
member declares an expression measure, all of one shape: the same number of
components, each read in the same carrier position by position. While one
member is certified, a call to any other member of its component owes that
member's own measure, read at the call, nonnegative and lexicographically
below the caller's entry reading, exactly as a self-call does. Every call in
the cycle then descends in one order
(`mdtests/c_decreases_pure_expression_mutual_recursion.md`, and the negative
`mdtests/c_decreases_pure_expression_mutual_recursion_must_descend.md`). A
member that declares no expression measure, or one of another shape, is
refused at the call that reaches it
(`mdtests/c_decreases_pure_expression_mutual_recursion_requires_every_measure.md`,
`mdtests/c_decreases_pure_expression_mutual_recursion_rejects_mixed_shapes.md`).
Click finds the component from the C call graph of the verified sources. A
measure over a resource binder's model, such as `decreases links_len(x.model)`,
is an expression measure too, so it ranks mutual structural recursion down a
data structure
(`mdtests/c_decreases_model_measure_mutual_recursion.md`).
A bare `int32` parameter uses those same call obligations. A self-recursive
`static inline` helper
with a contract is called through its contract, so an expression measure
ranks it like any function
(`mdtests/inline_helper_expression_measure_recursion.md`).

A binder the contract already declares names the same measure without
repeating its arguments:

<!-- verified-example: mdtests/c_decreases_matched_arm_child.md -->
```click
int32 tree_depth_ok(struct node* root) {
    owns t: tree_at(root);
    decreases t;
    ensures t.model == old(t.model);
}
```

An anonymous resource measure such as `decreases list(node)` must exactly
name an owned or viewed entry resource. Opening the ordinary contract proof
captures that resource's finite witness. Unfolding or observing its body
exposes owned children of the same family as strictly smaller witnesses;
observed children keep that evidence when projected to views. A fold builds
one parent above its supplied children, so rebuilding the original layer
does not turn the parent into a descendant. A freshly returned unrelated
resource receives no descent authority just because it has equal arguments.

Both self-recursive and mutually recursive calls owe these ordinary descent
obligations. The proof establishes guards and supplies the child through its
usual resource operations; there is no later walk over C to discover an
additional requirement. The C may consume or mutate resources, including
postorder deallocation. Descent concerns the finite resource witness rather
than a pointer value
(`mdtests/c_decreases_resource_mutating_nullable.md`,
`mdtests/c_decreases_resource_mutual_recursion.md`, and
`mdtests/c_decreases_resource_avoids_recursive_loop.md`).

A named binder measure is ranked at every call, for both self-recursion and
mutual recursion. Every member declares `decreases` on one of its own binders,
of a resource with a `match model` body, and the
instance a call passes for the callee's measured binder must hold a model
strictly contained in the model the caller's binder held at its entry. The
decision is the one a loop's `decreases` binder makes at its back edge: it
follows the arms the path's facts decide, so the unfold that exposed the child
is the evidence, and no size function is needed
(`mdtests/c_decreases_binder_measure_mutual_recursion.md`, and the negatives
`mdtests/c_decreases_binder_measure_mutual_recursion_must_descend.md` and
`mdtests/c_decreases_binder_measure_mutual_recursion_rejects_mixed_kinds.md`).

A loop measure is one component, or a nonempty lexicographic tuple of components, and each component
is any pure `int32`, unsigned, or mathematical `Integer` expression: a C
fragment, a
memory read, an application of
a pure Click function, a resource model field. Click evaluates the one
declared component at the iteration's entry state and again at the back-edge
state, exactly as it evaluates an invariant about the same cells at those two
states, and ranks the two values it gets. A component that reads memory owes
the same viewability an invariant reading those cells owes.

A component may read memory, as `decreases box->len - i` does for
a loop whose bound is a field the C keeps no local copy of: the read is
evaluated in the back-edge memory and again in the memory the iteration
started from, so a body that writes the cell is judged by what it wrote. See
`mdtests/loop_decreases_reads_a_field.md`,
`mdtests/loop_decreases_reads_a_field_the_body_writes.md`, and
`mdtests/loop_decreases_rejects_a_field_that_moves.md`. A measure is never
executed, so a read in it is not a C access; a volatile object cannot be
read, since its value is not a function of the state. A loop back edge must keep every component nonnegative and make
one component strictly smaller while keeping all earlier components equal. For
example, `decreases n - i` ranks a loop that increments `i` toward `n`.

A pure function of the cells the loop writes ranks a loop whose real measure
cannot be written in C:

<!-- verified-example: mdtests/loop_decreases_pure_expression.md -->
```click
loop {
  decreases head(box);
  invariant 0 <= box[0];
  invariant head(box) == box[0];
}
```

The application stays opaque, so the proof unfolds it where it has to. The
invariant `head(box) == box[0]` is the idiom that names the entry occurrence
for the closer: without it the back-edge goal holds two applications of `head`
at two memories and the closer has nothing relating either to a value it can
reason about. `decreases box[0]` would need the same `have`.

A measure must be a function of the current state alone, so a component may
not mention `old(...)` or `at(...)`. Such a component reads one fixed state
twice, so its two values are equal and the back edge could never close;
Click refuses it at the declaration and says so, rather than leaving a bundle
member permanently open. See
`mdtests/loop_decreases_rejects_a_state_measure.md`. A pure component earns
no leniency about the descent itself: a measure the body does not move leaves
the ranking member open exactly as a C one does, as in
`mdtests/loop_decreases_pure_expression_must_decrease.md`.

Arithmetic in every measure component is exact Integer arithmetic. For
example, `decreases 4 - x` means `4 - to_integer(x)`, including when `x`
is a narrow or unsigned counter:

<!-- verified-example: mdtests/a_uint8_loop_counter_ranks_as_a_promoted_int32.md -->
```click
loop {
    decreases 4 - x;
    invariant x <= 4;
}
```

The C increment still promotes a narrow counter to `int32` and narrows the
stored result. The closer proves the operation and cast identities from
the guard and invariant bounds before relating the two Integer readings.
Unsigned increments similarly need a no-wrap bound; `i < length` supplies
it even when `length` may be the largest value of its type
(`mdtests/a_fill_loop_over_a_size_t_range_needs_no_bound.md`).

A bare machine component such as `decreases x` keeps its carrier. Unsigned
components use unsigned order and have a trivial nonnegativity member;
signed components owe `0 <= x`. The unsigned countdown idiom
`while (x > 0u) x--;` uses the native unsigned order lemmas
(`mdtests/an_unsigned_count_down_loop_owes_an_unsigned_descent.md`).
Explicitly observing a machine expression, as in
`decreases to_integer(3u32 - x)`, retains its wrapping arithmetic. A back
edge on which that expression wraps upward is refused if the loop can
continue (`mdtests/an_unsigned_measure_that_wraps_upward_is_refused.md`). When
the next test is provably false, the exit owes no descent
(`mdtests/loop_numeric_descent_on_exit.md`). A plain
`decreases 3 - x` cannot wrap; it instead owes Integer nonnegativity and
strict descent. A `long` loop's `length - i` likewise ranks by an Integer
difference, without a signed 64-bit overflow obligation.

A component whose type is `Integer` ranks the loop in that carrier:

<!-- verified-example: mdtests/loop_decreases_integer_measure.md -->
```click
loop {
  decreases level(n);
  invariant 0 <= n;
}
```

Here `level(n: int32) -> Integer` returns `to_integer(n)`, so the bundle's two
ranking members are `0 <= level(n)` and `level(n_post) < level(n_pre)` over the
Integers. A lexicographic tuple may mix the carriers, because a pivot arm only
ever compares one component's two readings. The strictness is the same one an
int32 measure owes: `mdtests/loop_decreases_integer_measure_must_decrease.md`.
State the two members as `have`s before the body's last step, where they are
ordinary Integer goals with a Surface form, and the closer then has them as
exact facts.

A loop's ranking obligations are members of the back-edge invariant bundle,
not a separate kernel pass. When a loop declares `decreases`, the bundle the
back edge closes gains, after the invariants in declaration
order, one `0 <= component` obligation per declared component in declaration
order, then one decrease obligation. For a single component that obligation is
`post < pre`; for a tuple it is the disjunction over pivots, `post[0] < pre[0]`
or `post[0] == pre[0] and post[1] < pre[1]`, and so on, where `pre` reads the
component at the start of the iteration and `post` at the back edge. Choosing
the pivot is therefore an ordinary proof of one disjunct, closed with
`close()`, that the proof makes and [`click expand`](../cli/expand.md)
prints, not a search the kernel
performs. The back edge closes each of those members with `close()`, as it
closes each invariant and as a function's exit closes each `ensures`; where
`close()` misses one, prove it, or a fact it needs, with `have ... by { ... }`
before the back edge, for example by `close() using { ... }` naming the guard,
precondition, and invariant facts it needs. A missed member's diagnostic
names the ranking obligations the bundle carries.

The iteration's entry values are available as `at(region(N).entry, x)`, the
same form loop-body premises use. `close()` at the back edge reads the
facts in scope: the loop's declared invariants and guard at
iteration entry, the function's preconditions, and the C branch conditions
this path took to reach the back edge are among them.
<!-- verified-example: mdtests/c_decreases_lexicographic_loop.md -->
```click
loop {
    decreases (i, j);
    invariant i >= 0;
    invariant j >= 0;
    invariant j <= 2;
    ...
}
```
A C `if` the body took leaves its condition as a fact on that path, written
at the branching statement's entry as `at(region(N).entry, x)`. A measure
that depends on which arm ran closes from it: `stop_at_zero` leaves through a `break` inside an `if`, so the
only path that reaches the back edge is the one where `i == 0` was false, and
`0 < i` follows from that disequality and the declared `i >= 0`.
<!-- verified-example: mdtests/the_back_edge_cites_a_branch_condition.md -->
```click
loop {
    decreases i;
    invariant i >= 0;
}
```
A function-level numeric measure is compared with its immutable entry value.
The C parameter may be reassigned or addressed; the actual call must still
prove nonnegativity and strict descent. A decrement followed by a call on the
updated parameter is valid
(`mdtests/c_decreases_parameter_reassignment_descends.md`); an increment
followed by `n - 1` leaves the entry value unchanged and is refused
(`mdtests/c_decreases_rejects_updated_parameter.md`). Numeric loop measures
retain their own address-escape restrictions.

A loop may name one of its own resource binders instead of int32 components:
`decreases sub;` on a loop that declares `owns sub: tree_at(cur);`. The rule at
the back edge is that the instance the binder ends holding must be a strict
contained descendant, in the exact resource definitions, of the instance it held
at the loop head, with the submodel that child carries. A direct child is one
step of it; a body that moves two levels at once, as every rbtree fixup loop
does when it sets `node = gparent`, is accepted through the arms the path has
already decided. Each step down needs a premise naming that instance's
constructor, and the only thing that produces one is the body unfolding the
instance, so the walk follows the evidence the body left and stops where an
instance was never opened. Models are finite inductive terms, so a strictly
deeper submodel at every back edge is well-founded; there is no counter, size
function, automatic unfolding, or search. See
`mdtests/loop_decreases_strict_descendant.md`. Which arm names the children is decided by the loop's invariants
playing the part of a contract's requirements, the same arm selection contract
lowering uses, so a structural loop measure needs a `match model` resource
whose constructor the invariants pin down. Unlike the numeric components, the
structural descent is not a member of the invariant bundle: the back edge
decides it and names the binder when it does not descend. See
`mdtests/loop_decreases_rejects_same_instance.md`. Loop-local lexicographic tuples are supported; nested-loop
propagation treats a separately ranked inner loop as an opaque terminating
phase. If it writes a variable mentioned by the enclosing tuple, the kernel
forgets that variable's scalar alias and relies on the enclosing invariants for
the post-phase nonnegativity proof. Recursive calls inside loops remain
supported only when both obligations are proved independently: the loop needs
its own ranking, and every recursive edge still needs the function-level
measure. The loop guard is available when proving the recursive argument is
nonnegative. The numeric function-level measure must remain unchanged by
assignments, updates, allocation results, and call results. Structural
recursive calls in loops are supported for read-only resource transitions when
the parent is observed before the loop; the recursive call must still receive
a direct contained child. See
`mdtests/c_decreases_resource_recursive_in_loop.md`. A recursive call that
consumes a child inside a ranked loop is ranked by a model measure, and the
loop may free the node and continue
(`mdtests/c_decreases_model_measure_recursion_consumes_inside_loop.md`). A
call whose descent depends on the loop's changing counters is ranked by a
function-level expression or tuple measure, discharged from the loop
invariants (`mdtests/c_decreases_lexicographic_recursion_under_loops.md`).

Click certifies termination of the whole function, so every reachable loop and
recursive component must be ranked and every callee must itself have
termination evidence. Much of that costs nothing to write. A loop the proof
does not summarize needs no measure: Click executes such a loop concretely,
one bounded iteration at a time, and that execution succeeds only when every
feasible path has left the loop, so it is the loop's termination evidence; see
`mdtests/bounded_loop.md`. A loop proved through a `loop` block is summarized
by its invariants and needs a `decreases` clause. A verified callee supplies
its own; an `extern` contract is trusted to return, as its `ensures` is
trusted. Calls that form a directed acyclic graph are ranked by the planner's
call-graph heights, which are never written in source. A call through a
function pointer returns when every function whose address the project takes
returns without calling through a function pointer itself, directly or in
anything it calls. A comparator, visitor, or augment callback can meet that
rule. Click reports `unsupported` at the address-taking declaration when a
callback can reach an indirect call.

To support nested callbacks, a named callback contract would carry a
termination measure. An indirect call that can close a cycle would owe a
proof of descent under that measure. A finite chain through nested callbacks
should then verify, while self-application would still owe descent. See
`mdtests/termination_callback_self_application_rejected.md`.

An unranked loop or callee without a termination proof is an `incomplete
proof`. Click names the loop or follows the call to the missing proof.
Failure of `close()` to prove a supplied measure's nonnegativity or descent
is `unsuccessful search`. A function-level `decreases` clause requires a
recursive edge to rank. A function that promises to return also needs return
evidence for its calls. A call authorized by a contract that permits divergence
conflicts with that promise and reports a `contract error`.
The kernel records termination evidence separately from `VerifiedFunctionRule`,
so an ordinary `ensures` is still exactly a statement
about return states.

### Functions that may not return

A perpetual service loop is the exception, and it says so in the contract.
The `diverges` marker sits after the parameter list, beside `throws` and after
it when a signature carries both, and on a `loop` head, which has no signature
of its own:

<!-- verified-example: mdtests/diverges_perpetual_loop.md -->
```click
int32 wait_for_zero(int32 x) diverges {
    ensures result == 1;
} by {
    loop diverges {
        invariant x == x;
    }
}
```

The marker declares that the function, or that loop, may not return; it makes
no other claim and yields no evidence. A marked contract is judged by partial
correctness: safety is checked on every execution prefix, and the `ensures`
holds if the function returns. Because a marked function never
yields termination evidence, it cannot also carry a function-level `decreases`
clause, a marked loop cannot also carry a loop `decreases`, and a `loop
diverges` is refused unless its enclosing function is declared `diverges` too.
A marked function's other loops may still be ranked: their back-edge ranking
members are checked as usual, but the function still gives its callers no
whole-function termination evidence. An `extern` contract takes the marker in
the same signature position and still refuses `decreases`, since it has no
body to rank.

The marker is required on, and only on, a function that may not return. A
function whose every loop is ranked and whose every call descends has nothing
to justify the marker. Declaring it `diverges` reports a `contract error`
that asks the author to remove the marker. See
`mdtests/diverges_rejects_unjustified_marker.md`. An `extern` contract is
exempt, because the declaration is all that is known about it. The marker is
contagious: an unmarked caller of a marked function is refused, and the
refusal names the callee and the repair, which is to declare the caller
`diverges` too.

A named contract takes the marker in the same signature
position. A contract stands for an implementation this project need not name,
so the marker says that a call through a pointer carrying it may not return:
the function that makes the call must be declared `diverges` too, and the
refusal names the contract and offers the two repairs, which are that marker
or a contract without one. Such a call is itself what justifies the caller's
marker, so the unjustified-marker refusal does not then ask for it back; see
`mdtests/diverges_named_contract_requires_marked_caller.md`.

<!-- verified-example: mdtests/diverges_named_contract_in_marked_caller.md -->
```click
contract int32 Spinner(int32 x) diverges {
    ensures result == 1;
}

int32 run(int32 (*step)(int32), int32 x) diverges {
    requires Spinner(step);
    ensures result == 1;
}
```

Termination and host capacity are separate judgments. Click does not model
process stack exhaustion, address-space exhaustion, operating-system
allocation failure, or local-storage limits. A verified function can still
run out of those host resources; the worker's stack size and verifier budgets
are not program guarantees. The perpetual-loop regressions in the [examples
reference](../examples.md) pin what a `diverges` contract still promises.

### Grouped proofs

A function with several postcondition clauses may instead use one grouped
execution proof after the contract block:

<!-- verified-example: mdtests/grouped_function_proof.md -->
```click
int32 set_first(int32 p[], int32 value) {
    owns p[0..1];
    ensures result == value;
    ensures p[0] == value;
}
```

The trailing block executes the function once and proves, from that shared
execution, every listed claim that has no `by` of its own. It may also certify
a resource-only contract with no postcondition clauses. Its steps and its
implicit tail discharge the postconditions. A claim with its own `by` keeps that proof,
so one hard claim can be proved by hand beside a grouped proof of the rest; a
grouped proof that would prove no claim is refused. Structural region clauses,
including loop proofs, retain their own proof blocks.

When two or more claims omit their proofs and no grouped proof is written,
they share one omitted grouped proof, the implicit tail, so the default form
also executes the function once. `click expand` at the contract's closing `}`
writes that grouped proof out. A single claim without a proof has its own
implicit tail, which is the same proof.

For contracts that need only ordinary execution, loop checks, and closing,
omit the grouped proof. The implicit tail applies no theorems and folds only
a resource the contract produces whose body a returned path holds; write an
explicit grouped block for other folds and theorem applications.

Goal-specific pure reasoning can be isolated with `have`, including after the
function reaches its return frontier:

<!-- verified-example: mdtests/post_execution_have_witness_closes_exists.md -->
```click
step_until(function.exit);
have exists (k: int32) { k == result } by {
    witness(result);
    close();
}
close();
```

The scoped proof may use `obtain` and `witness`. Its established proposition
joins the facts of the one path at function exit, so the later `close()` can
use it to close the matching postcondition without applying those existential
steps to other contract claims.

Steps after `step_until(function.exit)` run in source order on that path.
`close()` closes the first open goal, and the implicit tail closes the rest.
Facts established after a closing step do not retroactively affect it. All
claim proofs for one path use the same finalized specification.

A proof is at one point at a time. Where the C splits into paths
that need different proof work at exit, write `branch` at the C `if`, or a
proof `if` before the C, each arm stepping to exit on its own path with
`step_until(function.exit)`. `step_until(function.exit)` never
splits: at a C branch the facts do not decide it is refused and names that
split. A proof `if` written after it is an ordinary case split on the one path
at exit, each arm adding its condition.

## Mathematical integers

`Integer` is the specification type for signed mathematical integers of
arbitrary size. It is separate from the C type `int` (an alias for `int32`).
Integer addition, subtraction, negation, and multiplication are exact and do
not generate machine-overflow obligations.

Integer is supported in specification bindings, typed `let` bindings, theorem
and pure-function parameters and results, quantifiers, datatype fields and
generic arguments, resource fields and patterns, and typed range folds.
Applications support exact Integer guards, explicit `using` premises, and
mixed Integer/C parameters. Unsuffixed decimal literals take their type from
an Integer expression, including values larger than 64 bits.
Machine variables and suffixed machine literals require explicit conversions. The signed int64 minimum is
`-9223372036854775808i64`: its magnitude is admitted only directly after
unary minus. The positive magnitude and values below this minimum are rejected.
`to_integer(value)` preserves the numeric value of each supported machine
integer type: `int8`, `int16`, `int32`, `uint8`, `uint16`, `uint32`, `int64`, and `uint64`.
Signed `-1` and unsigned `4294967295u32` therefore produce different Integers.
Evaluating the argument retains its C definedness obligations. For example,
`to_integer(x + 1)` requires established evidence of `defined(x + 1)`, even in
a reflexive comparison. This requirement survives aliases, nested arithmetic,
and conditional expressions; an overflowing C addition remains invalid.
`to_integer` of a `Nat` is its Integer value, and `to_integer` of an `Integer`
is that Integer unchanged.

The reverse names are `to_int8`, `to_int16`, `to_int32`, `to_uint8`, `to_uint16`,
`to_uint32`, `to_int64`, and `to_uint64`. Exact constants must lie within the
destination's range. Symbolic values require established lower and upper bounds;
for example, `to_int32(z)` requires `z >= -2147483648` and `z <= 2147483647`.
Missing either bound rejects the conversion, including inside reflexive claims.
No conversion wraps, truncates, or implicitly mixes the two types.
See [conversion examples](https://github.com/clicklang/click/blob/master/mdtests/integer_machine_conversions.md).

<!-- verified-example: mdtests/integer_successor.md -->
```click
theorem integer_successor(z: Integer) {
    ensures z + 1 > z by {
        close();
    }
}
```

Equality, disequality, and the ordinary order comparisons are supported.
`close()` can produce explicit arithmetic evidence for supported linear
comparisons. General multiplication is a valid expression; it does not imply
a general nonlinear arithmetic solver. Expanded proofs retain the arithmetic
evidence for ordinary verification to check.

Fold terms are checked opaque atoms in the supported linear certificate
fragment. An empty-range or append law supplies the fold step explicitly, and
the certificate retains the exact fold carrier, endpoints, body, and version
point of each read. Alpha-equivalent loads at one retained version point may
match; a different version point or a changed endpoint, body, or carrier does not.
The bounded affine planner uses selected checked premises and explicit
constant coefficients. It does not enumerate a range or introduce an
unchecked arithmetic assumption.

Integer values have no C storage or runtime representation. Datatype fields and
generic arguments such as `Box<Integer>` are supported, as is extraction from
known constructors. Symbolic Integer-valued datatype matches are supported when
the matched result has one consistent carrier; contextual Integer literals in
their arms inherit that result type. Mixed C and Integer arithmetic is
rejected unless an explicit conversion is present or the arithmetic is in a
position that expects an Integer
([Integer specification arithmetic](#integer-specification-arithmetic)).

### Integer specification arithmetic

Arithmetic on machine values takes its meaning from the type its result is
used at. Where there is no expected type, you must write one. Where an
Integer is expected, `+`, `-`, `*` and negation are exact Integer operations
and each machine operand is observed with `to_integer`, so `x + 1 > x` reads
`to_integer(x) + 1 > to_integer(x)` and holds for every `int32` and `uint32`.
Where a machine type is expected they are the C operation at that type:
partial, with a definedness obligation, for signed types, and wrapping for
unsigned ones. At an 8- or 16-bit type (`let s: uint8 = a + b;`, an
argument for a `uint8` parameter, the body of a `-> uint8` function),
`+ - * & | ^ ~` over operands of that type, or unsuffixed literals it holds,
are that type's own operators, which wrap modulo 2^8 or 2^16 at either
signedness and owe nothing
(`mdtests/narrow_specification_arithmetic_is_the_operator_at_its_type.md`,
`mdtests/narrow_arithmetic_at_a_narrow_result_or_parameter_is_native.md`);
a theorem's typed `let` names that native operation in its clauses and in
every proof step
(`mdtests/a_theorem_let_names_its_native_operation_in_a_proof_step.md`),
and `close()` relates its observation to its operands' by the in-range
identity, as at 32 and 64 bits, where bounds keep it from wrapping
(`mdtests/solve_plans_a_narrow_comparison_through_its_operation_identity.md`);
arithmetic there over an operand of another machine type is refused, naming
the conversion to write, such as `x as uint8`
(`mdtests/a_narrow_typed_let_of_mixed_operands_is_refused.md`); the operand
of a cast such as `(a + b) as uint8` has no expected type and keeps C's
promoted `int` operation. Unsuffixed literals are Integer unless their context gives
them a machine type;
compared with a 64- or 128-bit value, a literal is converted to that
value's format as C converts it, so `0 < v` on an `int128` reads
`0 < to_integer(v)`
(`mdtests/a_literal_compared_with_a_128_bit_value_takes_its_format.md`).

Specification `/` and `%`, which always have a machine type, are total. A
zero divisor leaves the kernel's opaque quotient or remainder: a fixed value
that nothing relates to anything but itself, not a chosen one. So
`a / b == a / b` and a function whose body is `total / count` need no
divisor premise, while `x / 0u32 == 0u32`, `x % 0u64 <= x` and `a / b <= a`
are not provable without one
(`mdtests/a_specification_quotient_needs_no_divisor_premise.md`,
`mdtests/a_quotient_by_zero_is_not_zero.md`,
`mdtests/a_quotient_by_a_divisor_that_may_be_zero_is_not_bounded.md`).
Signed `MIN / -1` and `MIN % -1` overflow their format, so a signed quotient
still owes `a != MIN or b != -1`, as signed `+`, `-` and `*` owe their range
(`mdtests/a_signed_specification_quotient_still_owes_its_overflow_exclusion.md`).
`defined(a / b)` states C's definedness and still includes `b != 0`. Executed
C and Rust division keep their undefined-behavior and panic checks: a C
function whose contract says `result == a / b` is still refused where `b`
may be zero
(`mdtests/a_total_specification_quotient_does_not_define_the_c_division.md`).
`truncating_quotient` and `truncating_remainder` still require a nonzero
divisor.

| Position | Expected type |
| --- | --- |
| an operand of a comparison that does `+`, `-`, `*` or negation, compares an Integer with a machine value, or has a `count(...)` operand | Integer |
| an argument for an `Integer` parameter of a pure function or theorem, including a library theorem and `truncating_quotient` / `truncating_remainder` | Integer |
| the value of `let s: Integer = ...`, an `Integer` constructor field, an `Integer` resource field's value in a `fold` map, the body of a `-> Integer` function | Integer |
| an arm of a `match` or a branch of an `if` in an Integer position (the `if`'s condition is a proposition) | Integer |
| a machine-typed parameter, constructor or resource field; `let s: int32 = ...`, whose unsuffixed literal value is an `int32` in the type's range; an index or memory range; a cast; the argument of `to_integer(...)` or `defined(...)`; an operand of `/ % << >> & \| ^`; a machine fold accumulator or body | that machine type |
| a `decreases` measure, and each component of a lexicographic one | Integer |
| an untyped `let s = ...` | none: arithmetic on a machine value in its value is refused; the binding has its value's type, so one whose value is an Integer is an Integer |

<!-- verified-example: mdtests/a_typed_let_gives_machine_arithmetic_its_meaning.md -->
```click
let s: Integer = a + b;
let t = a;
let k = 5 + 3;
```

`s` is the exact sum; `let s: int32 = a + b;` is C's sum and owes its
definedness (`mdtests/a_machine_typed_let_keeps_the_c_operation.md`). An `if` or `match` in an operand
is looked through: a comparison does arithmetic when a branch or arm does,
and each branch is then in the Integer position, so
`result == (if x < 7 { x + 1 } else { 7 })` reads
`to_integer(result) == (if x < 7 { to_integer(x) + 1 } else { 7 })` and the
branch's sum is exact, even at `INT32_MAX` or `UINT32_MAX`
(`mdtests/an_int32_branch_in_an_integer_comparison_is_exact.md`,
`mdtests/an_unsigned_branch_in_an_integer_comparison_does_not_wrap.md`).
`to_integer(if ...)` written out observes the C conditional instead, with
its branches' C obligations. An
untyped `let` of a plain machine value, such as `t`, or of arithmetic on
Integers and literals alone, such as `k`, needs no annotation. An untyped
`let` whose value does `+`, `-`, `*` or negation on a machine value, at its
top, under `old` or `at`, or in a branch or arm, is refused in a contract,
a theorem, a pure function body or a specification expression alike:
``untyped `let s` does arithmetic on a machine value; arithmetic takes its
meaning from the type its result is used at, so write `let s: Integer = ...;`
for the exact value or `let s: int32 = ...;` for the C operation``, naming the
operand's machine type where its source text shows it
(`mdtests/an_untyped_let_of_machine_arithmetic_is_refused.md`). So a value
never changes meaning when it is moved into a `let`. An untyped `let` has
its value's type, and an earlier `let` in scope (a contract's or theorem's,
or an enclosing `let ... ;`) is an operand of that type: after
`let a = to_integer(x);`, `let b = a + 1;` is Integer arithmetic and needs no
annotation (`mdtests/an_untyped_let_of_an_integer_has_the_integer_type.md`),
while after `let t = a;`, `let u = t + 1;` is refused and names `t`'s type
(`mdtests/an_untyped_let_of_a_machine_let_is_refused.md`). A typed `let`
gives an unsuffixed literal its machine type: `let m: int64 = 5;` is the
`int64` 5, for every fixed-width type
(`mdtests/a_typed_let_gives_a_literal_its_machine_type.md`), and a literal
outside the range is refused with
`` `let byte: uint8` cannot hold 300; a `uint8` lies in 0..=255 ``
(`mdtests/contract_let_type_mismatch.md`). An `Integer`
resource field's `fold` value is exact
(`mdtests/an_integer_resource_field_reads_fold_arithmetic_exactly.md`).
Predicates' `Integer` parameters and `Integer` resource parameters are not
supported yet, so neither is an Integer position. A contract `let` of a
machine value is a machine operand where it is used
(`mdtests/a_c_valued_contract_let_in_integer_arithmetic.md`). Integer
parameters, fields and results:
`mdtests/integer_parameters_fields_and_results_read_machine_arithmetic_exactly.md`;
match arms: `mdtests/a_match_arm_in_an_integer_comparison_is_exact.md`.

A comparison with a pointer (a parameter of a C function or a theorem, a
local, a struct field, a pointer `result`, or an `address(p)`) or a
floating-point value among its arithmetic operands, and a comparison without
arithmetic between machine values, keep their C meaning; the latter has the
same truth either way (`mdtests/pointer_operands_keep_their_c_meaning.md`).
Arithmetic on an address is pointer-word arithmetic, such as a tag added to
an aligned address
(`mdtests/address_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.md`,
`mdtests/pointer_arithmetic_on_a_theorem_parameter_keeps_its_c_meaning_under_integer_arithmetic.md`),
and a floating-point value has no Integer observation
(`mdtests/floating_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.md`).
A population count is a quantity, so a comparison with a `count(...)`
operand also compares Integers. Expansions and diagnostics print the
inserted `to_integer`, including when a native comparison observes a grown
population count (`mdtests/repeated_child_retains_grown_count_requirement.md`). See
`mdtests/integer_arithmetic_makes_specification_addition_exact.md` and its
C-arithmetic twin
`mdtests/machine_specification_addition_needs_its_overflow_bound.md`. The
standard library's own modules, under `library/`, read specification
arithmetic the same way; a library statement that means the C operation
observes its result exactly, as `integer::int32_increment_upper_bound`'s
`ensures to_integer(value + 1) <= to_integer(upper);` does, which is the
native comparison its kernel axiom states. The former migration directive
`arithmetic "integer";` is refused. A
specification that means C's wrapping unsigned result names it with the
[`integer` wrapping functions](../library/index.md#unsigned-wrapping-arithmetic),
such as `integer::uint64_wrapping_mul(state, k)`
(`mdtests/wrapping_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.md`);
written with `*` and `+` the same claim says the C step never wraps
(`mdtests/wrapping_arithmetic_written_as_integer_arithmetic_is_refused.md`).

An Integer comparison of exact observations of one machine type, such as
`0 <= to_integer(capacity)` or `to_integer(x) != to_integer(y)`, is the
native comparison `0 <= capacity` or `x != y`, because `to_integer` is
injective and preserves order: the kernel states it in that one form
([one form for comparisons of observations](../../internals/mathematical-integers.md#one-form-for-comparisons-of-observations)).
Built-in checks that read machine facts, such as resource quantities and the
definedness of a population count, therefore accept the Integer premise
(`mdtests/an_integer_bound_supplies_a_member_quantity.md`), and the fact is
exactly as strong in either form
(`mdtests/an_integer_premise_files_no_stronger_machine_fact.md`). The same
holds through an in-range machine `+` or `-`: `have a <= 4294967295u32 - b`
records `to_integer(a) <= 4294967295 - to_integer(b)`, which discharges
Rust's `u32` add check `a <= 4294967295u32 - b`, and the two Integer bounds
of `to_integer(a) - to_integer(b)` discharge C's `int32` definedness check of
`a - b`; a range bound the operand types do not imply must itself be a fact
([details](../../internals/mathematical-integers.md#one-form-for-comparisons-of-observations),
`mdtests/a_built_in_check_accepts_the_integer_reading_of_its_condition.md`). A constant
outside the type's range, or observations of two different types, have no
native form. An equality between a machine value and an Integer sum, such as
`to_integer(refs) == 1 + to_integer(amount)`, is not the C equality
`refs == 1 + amount`: the two agree only where the C sum is defined, which
`close()` proves through the operation identity.

An Integer equality over `+`, `-`, `*` and negation of 32-bit (`int32` or
`uint32`) observations and constants also establishes the equality of the
same expression in wrapping 32-bit arithmetic: reduction modulo 2^32 maps
each observation to its word and respects these operations. So
`to_integer(entry) - to_integer(capacity) == 0` establishes that the word
`entry - capacity` is zero, which a built-in check such as retiring a
population authority at count zero reads
(`mdtests/an_integer_count_equality_retires_its_authority.md`). Only this
direction holds, and only for equality: equal words do not make equal
Integers, so the word equality never decides the Integer one, and Integer
orders establish no word fact. A term of more than 64 nodes establishes
nothing.

A population count is an `int32` value like any other, observed as
`to_integer(count(R(p)))` whatever expression reaches it; `close()` relates
`to_integer(entry + quantity)` to `to_integer(entry) + to_integer(quantity)`
by the in-range operation identity. A signed definedness fact
`defined(a + b)` (or `-`, `*`) is exactly the two bounds
`to_integer(a) + to_integer(b) <= MAX` and `>= MIN`, and `close()` may cite it as
either bound
(`mdtests/solve_reads_a_definedness_premise_as_integer_bounds.md`). `close()`
selects Integer equalities over machine observations as rewrite candidates,
as it selects native equalities. An Integer count premise at entry serves a
`fold` over the grown count as its machine form does
(`mdtests/an_integer_entry_count_premise_folds_a_grown_count.md`).
A population's count at function entry is written `old(count(R(p, _)))`
in checked certificates, so a fact the kernel records about it, such as the
bound `count >= 1` a consumed member places on it, is cited like a written
premise
(`mdtests/a_consumed_member_bound_on_an_entry_count_is_cited.md`).
A total a mutex lock acquires is written
`at(statement(i).exit, count(R(p)))` for the lock's statement `i`: the count
where the lock returns. The lock's returned control holds the population's
authority, so the count can be read there and while that control stays
folded (`mdtests/a_lock_exit_reads_its_acquired_total.md`). A state that holds
no authority over the population, such as the lock's entry, has no readable
count (`mdtests/a_count_before_the_lock_is_refused.md`).
Resources may declare `field total: Integer;`: folding checks the resource's
facts, and `old(model.total)` retains the entry value across updates.
Checked resource pattern bindings retain each field's declared carrier, name,
entry or current point, and definedness while the pattern is lowered and
rechecked. See [resource field examples](https://github.com/clicklang/click/blob/master/mdtests/integer_resource_fields.md).

Pure functions with Integer parameters and results are supported. Calls remain
opaque until an explicit `unfold(function(args))` exposes the defining equation.
Arithmetic may treat an opaque result as an unknown Integer without unfolding.
A smart tactic may emit a checked unfold step; expansion makes that step visible.
See [the function example](https://github.com/clicklang/click/blob/master/mdtests/integer_function_successor.md).

A library function whose body is exactly `match s { V(.., x, ..) => x }`,
such as `slice::len`, is opaque in the same way: `slice::len(Slice<uint8>::Slice(p,
n))` lowers as that call, not as `n`, and `unfold` opens it to the field. The
goal is the same term whether the constructed value is written at the call or
arrives by `rewrite`
([example](https://github.com/clicklang/click/blob/master/mdtests/a_library_field_function_of_a_constructed_value_stays_a_call.md)).

Machine-integer `forall` and `exists` binders retain their declared width and
signedness, including `int64` and `uint8`. `intro`, `obtain`, and `witness`
preserve that type; a witness must have the exact binder type. Narrow integer
ranges stay scoped to the quantifier: introducing a universal supplies the
fresh value's intrinsic bounds, and existential witnesses must satisfy their
bounds. A `uint8` witness therefore lies in `0..255`, and an `int64` witness
keeps its high bits. One `intro()` introduces a narrow universal and reaches
its written body; no extra introductions are needed for type bounds.
Arithmetic in quantified bodies still requires its ordinary definedness checks.

Integer and mixed C/Integer quantifiers support checked introduction and
instantiation over their logical, unbounded domains. Integer range folds support
typed scalar bodies and checked empty and append laws for `Int32` and `Integer`;
expansion preserves those checked applications. Array- and memory-reading fold
bodies use scoped definedness and exact version points. Integer existential
witnesses may contain indexed reads when their viewability and conversion
obligations are checked. A complete C loop proof still needs its own prefix,
intermediate definedness, and loop-invariant obligations; range folds do not
enumerate a symbolic array to discharge those obligations.
Checked conversions between `Nat` and `Integer` are available; implicit
conversions to C integers are not.
Division and remainder are deferred; when implemented they will use Euclidean
semantics. Bitwise operators remain unavailable for `Integer` values. See the
[mathematical Integer internals](../../internals/mathematical-integers.md) for
the supported coverage, definedness rules, and deferred work. `Nat` remains the
existing [structural natural-number datatype](../library/index.md#natural-numbers).

## Pure theorems

Pure theorem declarations prove Click propositions without attaching the proof
to a C function:

<!-- verified-example: mdtests/pure_theorem.md -->
```click
theorem preserves_assumption(x: int32) {
    requires x >= 0;

    ensures x >= 0;
}
```

Like every Click-native declaration, theorem parameters use `name: type`
syntax. A symbolic callback uses a nameless C function-pointer declarator
as its type, for example `step: void (*)(int32*)`; the bound value remains an
ordinary function pointer, and behavioral knowledge remains an explicit
`Contract(step)` proposition. A theorem body uses the same contract-block shape as C function
specs: immutable `let` bindings,
proposition `requires` clauses, and proposition `ensures` clauses with proof
clauses. A theorem-only `.click` file does not need a `verifying "file.c";`
declaration.

A generic theorem or pure function can declare `p: T*`, and a pure function
can return `T*`. Applications infer `T` from the argument's pointee type and
require repeated occurrences to agree; a `T*` result is the instantiated
pointer type, so `id(p) == p` compares `int32*` with `int32*`
([`a_generic_pointer_result_is_its_argument_pointer_type.md`](https://github.com/clicklang/click/blob/master/mdtests/a_generic_pointer_result_is_its_argument_pointer_type.md)). Native
scalar, pointer, and struct element types retain their identity when instantiated.
For a struct element, range lowering looks up its physical size, including padding,
in the imported C layout. The generic declaration does not require a concrete
layout. This permits `p: T*` with `T = struct Foo`; it does not introduce a
struct-by-value logical parameter `x: T`. Instantiation supplies the declared
stride, not original-object provenance or permission to access memory.
See [`separation::contains_subrange`](../library/index.md#separationcontains_subrange).

`Resource` is a theorem-parameter type for resource descriptors. For example,
`theorem transport(A: Resource, B: Resource) { requires separate(A, B);
ensures separate(A, B); }` accepts `memory(...)`, a declared resource
application, or another resource parameter as an argument. A descriptor carries
no ownership. Arguments are evaluated in the caller before substitution, so
callee parameter names cannot capture names inside them. This type is currently
limited to theorem parameters; it is not a C type or an ownership clause.
See [`separation::separate_restrict`](../library/index.md#separationseparate_restrict) for an
explicit separation axiom and its checked field-separation example.

Resource expressions also include separating conjunction `A * B` and the empty
resource `separation::emp`. The operator associates to the left; parentheses
select grouping. It combines resource requirements and retains repeated
components, rather than deduplicating them as a set union. These expressions
are descriptors used in theorem arguments, `contains`, and `separate`; they
neither grant ownership nor open resource instances. Use the named laws in
`click::separation` to reason about components explicitly.


Theorems are intentionally pure. They do not support `owns`, `consumes`,
`produces`, region proof blocks, `old(...)`, `at(...)`, or
`result`: applying a theorem lends, consumes, creates and separates nothing.

One resource clause does have a reading without a resource context. `views
v[lo..hi];` states that reads of the range are defined, which is an ordinary
hypothesis, so a theorem accepts it and lowers it to the proposition
`viewable(v[lo..hi])` states, in the position it was written:

<!-- verified-example: mdtests/theorem_views_states_a_readable_range.md -->
```click
theorem cell_of_a_viewed_range(v: int32[], lo: int32, hi: int32, k: int32) {
    views v[lo..hi];
    requires lo <= k;
    requires k < hi;
    ensures to_integer(v[k]) == to_integer(v[k]) by close();
}
```

Nothing is lent by writing it and nothing is returned. Like every stated range
it carries its valid-span facts, which the theorem's proof assumes and an
application owes; see [Viewable ranges](../../concepts/viewability.md). The
range premise can be stated with `have viewable(v[lo..hi]);`.

Pure theorem scripts can simplify, unfold predicates and pure functions, apply
theorems, introduce logical structure, rewrite, use exact assumptions, and
derive atomic propositions. They cannot execute C or transform resources.
Applying a theorem never consumes, creates, returns, opens, or closes
resources. The exact inventory is in the
[proof tactics reference](../tactics/index.md).

One theorem form is not pure. An `executes` clause gives a theorem a single
call as its execution frontier, together with the resources, `old(...)`, and
`result` that one call needs. See
[Callback execution theorems](#callback-execution-theorems).

Pure theorems can use explicit strong induction on an `int32` or `uint64` parameter:

<!-- verified-example: mdtests/pure_induction_countdown.md -->
```click
theorem countdown_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown(n) == 0 by {
        let ih = induct(n);
        if n <= 0 {
            unfold(countdown(n));
            close() using { n <= 0; };
        } else {
            have 0 <= to_integer(n - 1);
            have to_integer(n - 1) < to_integer(n);
            apply(ih(n - 1));
            unfold(countdown(n));
            rewrite(countdown(n - 1), 0);
            close();
        }
    }
}
```

Scalar `induct` may follow earlier helper proofs while the original theorem
goal remains focused. The facts available at that step must establish that
its parameter is nonnegative. `ih(m)` is available after that declaration and
requires `m` to be nonnegative and strictly smaller, plus all theorem
requirements after substituting `m` for the induction parameter. Other theorem
parameters remain fixed. This is a pure proposition rule. `apply(ih(m))` checks
those fixed obligations against the facts already in scope. Use `have` to
establish a missing premise. Expansion keeps the same application.

Pure-function calls can be opened explicitly with
`unfold(function(args))`. This simple operation exposes one defining equation
at the current proof state. It never recursively expands the resulting call
tree; a recursive call in the selected body remains opaque until a later
explicit unfold. Lowering never executes a pure Click function, even when all
of its arguments are concrete: the application remains a typed logical term
until such an unfold step is requested. Likewise, `match` over an unknown
algebraic value remains one symbolic match term; it does not split C execution
paths. A match reduces directly only when its scrutinee is already a checked
constructor. This includes algebraic-valued matches whose scrutinee becomes a
constructor after `rewrite`: normalization selects the arm and substitutes its
typed fields without capturing variables in nested matches. It does not unfold
pure calls in that arm. See
[`normalize_algebraic_match_after_rewrite.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_algebraic_match_after_rewrite.md).

Theorems can be reused by explicit application:

<!-- verified-example: mdtests/pure_theorem_apply.md -->
```click
theorem nonnegative_body(x: int32) {
    requires nonnegative(x);
    ensures x >= 0 by {
        unfold(nonnegative(x));
        close();
    }
}

theorem reuses_nonnegative_body(y: int32) {
    requires nonnegative(y);
    ensures y >= 0 by {
        apply(nonnegative_body(y));
        close();
    }
}
```

Proof-level `if` performs explicit case analysis on a pure proposition. It
checks the same current claim under the proposition and its negation:

<!-- verified-example: mdtests/proof_if_cases.md -->
```click
theorem int32_sign_split(x: int32) {
    ensures x <= 0 or x > 0 by {
        if x <= 0 {
            close();
        } else {
            close();
        }
    }
}
```

The same construct can appear before or after C execution in a function proof.
It splits proof reasoning only; it does not itself execute a C `if` statement.
Inside a case, `step()` uses the case fact to enter the selected C arm.

When a C `if` is at the execution frontier, use `branch` instead of repeating
its condition as a logical case split:

<!-- verified-example: mdtests/proof_branch_old_state_interface.md -->
```click
branch {
    true => {
        step();
    }
    false => {
        step();
    }
}
step();
```

`branch` reads the guard from the C source and enters every feasible arm. Each
nonreturning arm must stop at the C `if`'s shared continuation, after which the
following proof continues once from one joined state. An arm that returns
closes its own outcome inside the arm; it does not run the continuation after
`branch`. The tactic fails if the current frontier is not a C `if`.

A transition sees every fact in the proof context. When a statement's
prerequisite is not yet available, establish it with `have` before the step:

<!-- verified-example: mdtests/simple_statement_step_requires_exact_prerequisite.md -->
```click
step();
```

At a loop entry, `loop { ... }` verifies initialization and one arbitrary
iteration, constructs the kernel loop rule, applies it, and reaches the
abstract exit. It fails if the current frontier is not a loop. Ordinary
`step()` instead evaluates the loop condition and enters at most one concrete
iteration; it does not invent a loop summary.

A loop header holds `invariant` items, an optional `decreases` clause, the
`initialize` and `maintain` phase proofs, and the loop's own resource clauses.
Those resource clauses take the same forms a contract's do, including the
instance binder `owns name: resource(args);`. A declared binder takes the one
enclosing owned instance of that family and arguments, the invariants may read
`name.field`, and the back edge binds the name again
from the family and arguments rather than from whatever the body called the
instance. Instances the loop does not declare are unavailable in the body and
returned after it. A declared binder's arguments are read where they are used:
the head builds the binder's instance at the loop's own havocked values, and
the back edge reads the clause again in the state the body reached, so a body
that assigns `root = root->left` hands the loop the instance at the new cursor.
A loop's `decreases` may name one of its binders, which is the structural
measure below. Instances the loop does not declare are unavailable in the body
and returned after it. The rules are in
[loops and invariants](../../concepts/loops-and-invariants.md).

When the two arms need to expose facts or resources about changed state, add an
optional common-frontier interface to `branch`:

<!-- verified-example: mdtests/proof_branch_interface_continuation.md -->
```click
branch ensuring {
    fact y >= 0;
} {
    true => {
        step();
    }
    false => {
        step();
    }
}
step();
```

Every continuing arm must prove every listed pure or resource fact. The
interface augments the deterministic common state; it is not an exhaustive
whitelist, so exact common facts and resources remain available without being
restated. Arm-only information is forgotten. If plain `branch` cannot form a
useful deterministic join, Click asks for an `ensuring` block rather than
retaining hidden path states or searching for an interface.

Statement IDs are global within a function and follow source preorder. An
`if` or loop receives its ID before statements nested in its arms or body; a
sequence does not receive a separate ID. The same IDs name execution targets,
annotations, and the points `at(region(N).entry|exit, ...)` reads at.

A frontier-local loop tactic may give the loop it encounters a stable name
with `loop label { ... }`.  The label names that encountered loop's entry
and exit points; it never searches for or jumps to a source region. A
label names one loop on an execution path: a second `loop label` at a
different loop is refused. Use
`at(label.entry, expression_or_proposition)` and
`at(label.exit, expression_or_proposition)` after the tactic has established
those points. Intermediate propositions are proved with `have` in the ordinary
forward proof, so they use the resources, premises, and execution frontier
established by the preceding tactics rather than starting a separate traversal
from function entry.

`apply(...)` instantiates a verified theorem, requires each proposition
`requires` clause as an exact current pure fact or a context-free tautology,
and adds its proposition `ensures` clauses as derived facts. It does not search
the context for an implication that would establish a missing premise, and it
does not change the current resource context. Theorem declarations are checked in source order after the standard
library, so a theorem proof can apply stdlib theorems and earlier theorem
declarations. C function proof scripts can apply any verified theorem from the
standard library or the current file. Before function exit, `apply(...)`
immediately adds its conclusions to the current pure facts, so they can justify
the next `step()`. After function exit it is checked separately on each
path, where `result`, post-state expressions, and ordinary `old(...)` arguments
can be evaluated.

## Callback execution theorems

An ordinary theorem has no execution frontier. An explicit `executes` clause
instead proves a contract implication by checking one arbitrary callback call:

<!-- verified-example: mdtests/c_contract_executes_buffer.md -->
```click
resource Buffer(data: int32*, count: int32) {
    owns data[0..count];
}
contract void Raw(int32* data, int32 count) {
    requires count >= 0;
    owns data[0..count];
}
contract void Buffered(int32* data, int32 count) {
    requires count >= 0;
    owns Buffer(data, count);
}
theorem raw_is_buffered(callback: void (*)(int32*, int32))
    executes callback(int32* data, int32 count)
{
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data, count));
        step(Raw);
        fold(Buffer(data, count));
        close();
    }
}
```

The premises state the source contracts for that callback, and the conclusion
states the target. The proof starts with arbitrary call arguments and the
target contract's requirements and resources. It knows the premises and
whatever its own checked steps establish, never the target fact being proved.
The call checks the selected source contract's requirements and performs its
resource transition. The rest of the proof must establish the target's
guarantees, return its resources, and stay inside its write footprint.
Unrelated owned resources use ordinary framing.

These are ordinary execution proof blocks: `have`, theorem application,
rewriting, proof cases, `fold`, `unfold`, and the usual closing tactics retain
their normal meanings. Every feasible proof case must execute the call exactly
once. The checked result is a reusable contract implication:
`apply(raw_is_buffered(f))` establishes `Buffered(f)`, after which an ordinary
caller can use `step(Buffered)`. Expansion preserves the explicit contract
selection.

Return-valued callbacks use the same syntax: the theorem parameter's C
function-pointer type supplies the return type. `step(Contract)` performs the
call and forwards its actual return value to `result` in one checked step.
The proof may relate `result` to current or `old` memory and to guarantees
from other applicable contracts. There is no extra proof step to expose the
result, and no new result-binding syntax. Existing supported scalar and pointer
return types retain their C types. See the
[end-to-end return-valued buffer proof](https://github.com/clicklang/click/blob/master/mdtests/c_contract_executes_status.md).

An explicit proof `if` after `step(Contract)` may distinguish success and
failure using `result`. Conditional postconditions remain conditional until
their guard is established; `apply(fact)` exposes the selected consequence.
Each case must return the target resources, and failure does not inherit
success's update guarantee (nor success failure's preservation guarantee).
The [status-returning callback tests](https://github.com/clicklang/click/blob/master/mdtests/c_contract_executes_status.md)
cover this refinement and an ordinary C caller that checks the returned status.
These proof cases may nest: each inner arm receives its own condition, and
the continuation after an inner `if` must check in every reachable case.
See the [nested status cases](https://github.com/clicklang/click/blob/master/mdtests/c_contract_executes_status_nested.md),
including an impossible arm and a shared continuation containing another case.

A callback theorem has one nongeneric callback parameter, one
target-contract conclusion, and one or more source-contract premises for that
same pointer; additional theorem parameters are refused.
Const-qualified pointer returns and parameters use the same C syntax in
callbacks, named contracts, and execution proofs.

### Names in an execution proof

Nothing enters an execution proof block implicitly. Exactly three forms
introduce names:

- the `executes` parameter list introduces the call's C parameters;
- `as { parameter: name }` on the conclusion introduces one arbitrary instance
  per resource handle of the target contract;
- `let { binder: name, ... } = step(...)` introduces instances a callee
  `produces`.

Every other name in the block is one of those, a theorem parameter, or
`result`.

The `executes` arguments use C parameter syntax and match the callback
signature. They are bound only inside the execution proof; they cannot escape
into theorem premises or conclusions. Their names must be distinct from the
callback and from `result`; a return-valued callback parameter also cannot be
named `result`.

When the target contract declares resource handles, the conclusion
introduces one arbitrary instance per parameter with an `as` map keyed by the
contract's parameter names:

<!-- verified-example: mdtests/c_contract_executes_counter.md -->
```click
theorem lift(callback: int32 (*)()) executes callback() {
    requires Exact(callback);
    ensures Progress(callback) as { cell: k } by {
        step(Exact, { cell: k });
        have k.revision == old(k.revision) + 1 by close();
        close();
    }
}
```

`k` is the only name for that instance inside the block, and the theorem proves
the refinement for an arbitrary such instance. The target's own name `cell`
is not in scope. Every target handle must be named exactly once, and
an introduced name cannot shadow the callback, the call arguments, a theorem
local name, or `result`. The names do not escape the block. A target with no
handles takes no map, though an empty `as {}` is accepted, and a map
on such a target is an error. Source and target parameter names are unrelated,
and the target contract may be declared later in the file.

A step passes instances by the binder names the callee's own declaration
fixes. Both a named contract and a C function declare their binders in
`owns`, `consumes`, and `produces` clauses, so `step(Exact, { cell: k })` and
`step(increment, { first: k })` use the same map, as in
[Calls that transport named instances](#calls-that-transport-named-instances).

The [counter refinement tests](https://github.com/clicklang/click/blob/master/mdtests/c_contract_executes_counter.md)
demonstrate an exact field increment refined to progress while framing an
unrelated caller-owned counter. Unmentioned fields of the selected counter are
not implicitly preserved.

### Concrete callees

`executes` may also name a verified or explicitly external C function instead of
a callback parameter. The theorem then has no callback parameter and no
source-contract premise: the source is that function's own checked contract,
run by the single call step.

<!-- verified-example: mdtests/c_contract_executes_concrete.md -->
```click
theorem increment_is_exact() executes increment(int32* state) {
    ensures Exact(&increment) as { cell: c } by {
        step(increment, { first: c });
        close();
    }
}
```

The conclusion chooses the form: a function address selects the concrete route,
a plain binding the abstract one. The proof state still starts from the target
contract's requirements and resources with the `as`-introduced instances bound,
and the call is the ordinary C call of
[Read and write resources](#read-and-write-resources). The written parameter
list restates the C signature as well as the target contract's interface, and
the callee must be verified or explicitly external in the project. Extra
theorem parameters are refused, and every feasible proof case must
execute exactly one call, as in the abstract form.
`apply(increment_is_exact())` then introduces `Exact(&increment)` at a call site
exactly like a concrete `unfold(Name(callback))` refinement theorem. This is the explicit
route for a target contract with resource handles, which `unfold(Name(callback))` refuses.
The [modeled-instance variant](https://github.com/clicklang/click/blob/master/mdtests/c_contract_executes_concrete_model.md)
carries a tree instance through the same two maps.

A concrete `static inline` callback uses its ordinary source name in both
forms of refinement theorem. The contract fact refers to the same
translation-unit-local function as a C initializer or call. If multiple
translation units define that name, Click does not choose one or identify
their function pointers. The [inline callback regression](https://github.com/clicklang/click/blob/master/mdtests/c_contract_inline_callback.md)
checks both refinement forms and a static const callback table.

### Automatic formation at `&f`

Passing `&f` where a named contract is required does not always need such a
theorem. Formation compares the two interfaces over one shared symbolic entry
memory and one shared post-call memory, so `old(pointer[0])` denotes the same
entry value on both sides. A contract whose clauses read no memory forms on
that comparison alone. When any clause reads memory, the named contract must
also declare resource requirements, resource guarantees, and a nonempty owned
footprint. In both cases the concrete function's owned footprint must be
contained in the named one, and a footprint guard on either side must be
load-free.

Formation admits scalar comparisons and `defined` over current and
function-entry memory, the connectives and quantifiers over those, finite
sequence comparisons, reads of a resource instance's fields on either state,
algebraic equalities, `match` over an algebraic value, and algebraic arguments
to a pure function. It excludes `at(...)`, reads at any other point,
population counts, range folds, and mathematical `Integer`
comparisons.

Every admitted clause must also follow by an exact route: the clause is already
an available fact, or it is one condition the decision procedure settles.
Formation chooses no disjunction arm, refutes no guard it would have to reason
about, and searches no equality for a rewrite. A clause outside the admitted
classes, or one needing any of that reasoning, is proved by an explicit theorem
instead.

When the contract declares resource handles, formation also requires the
pairing between its parameters and the implementation's binders to be forced:
for each parameter exactly one binder of the same resource family with equal
arguments, and the reverse. Two binders of one family, or a binder with no
counterpart, leaves the pairing unforced. The resource family alone decides
this, so two binders of one family on either side refuse even when their
arguments differ and only one pairing could match. Click then refuses
rather than choosing one, and prints the `executes` theorem that states the
pairing, with the contract's `as` map and the implementation's binder map
filled in.

## Requirements

Requirements are shared by all guarantees for the function.

Supported structural requirements:

<!-- verified-example: mdtests/structural_requirement_forms.md -->
```click
requires n >= 0;
requires viewable(p[0..n]);
requires viewable((p + 1)[0..1]);
requires separate(memory(dst[0..n]), memory(src[0..n]));
requires same_allocation(begin, end);
requires defined(x + 1);
views p[0..1];
consumes p[0..1];
```

`requires` clauses take no label: a proof cites a precondition by its
proposition, and an unmet one is reported by its text. An `ensures` label
names its postcondition claim. A loop `invariant` may be labeled the same
way, and the label names it where a failure reports it: "loop 0 invariant
`bounded` entry" for `invariant bounded: i <= n;`. To open an available existential precondition, write its
proposition with `let k = obtain(exists (x: Type) { ... });` or
`let k = obtain((lo..hi).any(|i| { ... }));`.

`viewable(base[start..end])` and `memory(base[start..end])` use half-open
integer element ranges. The byte count is derived from the base pointer's
element type: four bytes for `int32[]`, one byte for `uint8[]`. This `..`
syntax is Click contract syntax, not C fragment syntax.

A memory descriptor also accepts a saved pointer base:
`memory(old(p)[i..j])`, `memory(at(mark, p)[i..j])`, or the single-cell form
`memory(old(p)[i])`. Only the base selects the saved state; the indices are
evaluated in the surrounding state. This differs from
`old(memory(p[i..j]))`, which selects the earlier state for the whole descriptor.
The descriptor grants no ownership and discovers no preservation facts.
See `mdtests/saved_memory_bases_keep_current_indices.md` and
`mdtests/saved_memory_indices_do_not_freeze_at_entry.md`.

`viewable(R)` is a pure, point-dependent proposition for a resource
descriptor `R`, including resource parameters, named resources, and separating
conjunctions. It grants no ownership. The legacy segment form
`viewable(base[start..end])` is equivalent to
`viewable(memory(base[start..end]))`. Use it where Click expects a proposition,
such as a composite resource `fact`. The axiom
`separation::viewable_restrict(A, B)` derives `viewable(B)` from explicit
`viewable(A)` and `contains(A, B)` premises.

`defined(expression)` is a [special form](#special-forms): a pure proposition
stating that the expression's root operation reaches a value rather than
undefined behavior, with its operands taken as values. Click elaborates the
operation with the kernel's C expression semantics, so signed overflow,
division, shifts, and memory-load conditions share the same rules as execution.
An operand's own domain is not part of the claim: it is owed wherever the
expression is written, as for any term. So `defined(a + b + c)` claims that
adding `c` to the value of `a + b` is defined and owes `a + b`'s domain
(`mdtests/defined_owes_its_operands_domains.md`); both domains are
`defined(a + b) and defined(a + b + c)`, which also serves as a guard, since
the right side of `and` is read only where its left side holds
(`mdtests/defined_claims_its_root_operation_with_operands_as_values.md`).

A form without a single root operation reads through to one. `let` binds its
value, whose domain is owed, and claims its body's operation; a `let` whose
body is its bound name, as a Click function or lambda application binds its
result, claims that value's operation, so `defined(read(1))` for
`read = |i: int32| -> int32 { p[i] }` claims the read of `p[1]`. A cast to its
operand's own type claims the operand's operation; any other conversion is the
operation. `if c { x } else { y }` claims
`(c implies defined(x)) and (not c implies defined(y))`, and a `match`
claims each arm's body where its pattern matches, with the scrutinee as an
operand (`mdtests/defined_of_a_match_claims_its_taken_arm.md`,
`mdtests/defined_of_a_match_owes_its_arms_operands_domains.md`). Every other
form is its own root: a call's arguments, a conversion's Integer operand, a
`count(...)`'s arguments and a fold's bounds and initial value are operands,
while a fold claims every pass of its body
(`mdtests/defined_owes_its_integer_operands_domains.md`,
`mdtests/defined_of_a_fold_owes_its_bounds_domains.md`). In a C fragment the
same holds operator by operator, `?:` reads as `if`, and `&&` and `||` claim
nothing of their own, owing their right side's domain only where the left
does not decide the result. A form with no operand expressions, such as a
variable or a literal, is defined.

For two object pointers, `defined(right - left)` is C's precondition for
pointer subtraction (C11 6.5.6p9): both point into the same array object, or
one past its end, and their element distance fits in `ptrdiff_t`,
which is `int64` on this target. The model's pointer coordinates are signed 32-bit,
so on this target shared provenance implies the distance fits
(`mdtests/c_pointer_distance_widens_coordinates.md`). It implies
`same_allocation(right, left)`. A modular pointer-distance helper can use that
single requirement; a concrete same-array caller, including one using its
one-past endpoint, discharges it from the pointer objects and their offsets.

`same_allocation(left, right)` states that two object pointers were derived
from the same allocation: the same variable instance, heap allocation, or
literal (C's storage instance, Rust's allocation). It is C's precondition for
relational pointer comparison (C11 6.5.8p5) and Rust's for `offset_from`,
between independently supplied pointer parameters. Pointer arithmetic
preserves it, so the fact also covers pointers derived from either argument.
It does not say that the pointer values are equal, grant access to pointee
memory, or replace an `owns`, `views`, or `viewable` clause. Conversely,
pointer equality does not establish `same_allocation`: equal addresses can
carry provenance from adjacent allocations. A null pointer has no provenance,
so `same_allocation(0, 0)` is false even though the pointers compare equal.
The caller must establish the relationship from its concrete pointer objects,
a nonempty `viewable` proposition or memory resource, or its own retained
`same_allocation` requirement. An empty viewable or memory range does not
establish that its base has object provenance.

`aligned(pointer, n)` states that the pointer's address is a multiple of `n`,
a power of two. It is sugar for `(address(pointer) & (n - 1)) == 0`. Click
decides it from how the pointer was formed, never from its pointee type: a
successful heap allocation is 16-byte aligned; a declared local's block is
aligned for its type from its declaration, a struct local's for its
layout; a file-scope or static object's block is aligned for its type from
its creation; and a pointer reached through a parameter
needs an `aligned` clause in a contract or a `fact` in a resource. A
required complete-object clause `*p` for a struct type carries
`aligned(p, alignof(struct))` as a generated requirement: the caller proves
it and the function relies on it. A produced object and a resource body
state alignment explicitly, with `ensures aligned(result, n)` and
`fact aligned(p, n)`. A
constant byte displacement from such a base is then decided exactly, so
`aligned(p + 1, 8)` is refuted when `aligned(p, 8)` holds, and a symbolic
element step whose scale the alignment divides keeps it, so `aligned(p + i, 8)`
holds for an 8-aligned `struct pair *p`. Other symbolic displacements and
pointers without evidence stay undecided.

`requires` can also use Click propositions, but direct memory reads in
requirements are intentionally limited. If a precondition needs memory reads,
package it as a named predicate and unfold it at proof sites when needed.

## Read and write resources

Memory resources have viewed and owned resource elements. `views
base[start..end]` borrows read access and keeps that range unchanged and
allocated for the borrow; `owns`, `consumes`, and
`produces` supply write access with the transfer behavior described below.
These are resource facts, not classical predicates, and are carried in the
verifier's resource context rather than copied as pure facts.

<!-- verified-example: mdtests/resource_context_write.md -->
```click
int32 write_next(int32 p[], int32 x) {
    owns p[0..1];
    requires x < 2147483647;

    ensures returns_written: result == p[0];
    ensures writes_next: p[0] == x + 1;
}
```

Permission checking is mandatory for external memory. External loads require a
covering viewed or owned memory resource, and external stores require a covering
owned memory resource. Resource ranges use the element width of the pointer expression,
so `int32 p[]` ranges count four-byte cells and `uint8 bytes[]` ranges count
bytes. Local stack accesses do not require resources. A function with no
resource context has no permission to access external memory.

An index or a range bound keeps the integer type the source gives it. A range
from zero to a `uint64` bound, the shape a `size_t` or `usize` length gives,
has 64-bit bounds, and an element at a `uint64` index is placed in it by
64-bit comparisons. Nothing is cast and the contract states no limit on the
length. The range itself carries the object-size limit,
`length <= 9223372036854775807` divided by the element width, which holds of
any object. A range with a nonzero start, or a signed 64-bit bound, is still
read through 32-bit indices and needs its bound shown to fit.

A callee's constant range at a pointer into such a range, the `chunk[0..4]`
of `first_of_four(bytes + index)`, is covered by it when `index <= length`
and `4 <= length - index`
(`mdtests/a_callee_takes_a_window_of_a_64_bit_range.md`). This holds for
`views`; an owned window is not split out of an owned 64-bit range.
A window two `size_t` offsets deep, `first_of_four(chunk + index)` with
`chunk` at `bytes + start`, is at index `start + index` when each offset is
at most `9223372036854775807`; a call that leaves fewer than four elements
after `start + index` is refused
(`mdtests/a_window_two_offsets_past_the_end_is_refused.md`). A loop that holds
a chunk of the range, `views chunk[0..16]`, lends a callee any part of that
chunk without placing it in the whole range
(`mdtests/a_callee_reads_inside_a_chunk_a_loop_holds.md`).
A stored cursor can name the same window when a checked equality relates it
to the input's native index. Address normalization and the cursor's indexed
alias are checked separately; the alias supplies no access authority and the
complete span still needs its unsigned bounds. The cursor and short-span
regressions are in
`mdtests/a_callee_takes_a_wide_window_through_a_checked_cursor.md`.

A cast written in a place keeps its meaning: `bytes[index as int32]` is the
element at the truncated index, which is not the element the code reads at
`bytes[index]` (`mdtests/a_cast_in_a_place_reads_the_truncated_index.md`).
A cast written in a range bound does the same: `bytes[0..length as int32]` is
the range up to the truncated length, read through 32-bit indices, and does
not hold the element the code reads at a 64-bit index
(`mdtests/a_cast_in_a_range_bound_truncates_the_bound.md`).

<!-- verified-example: mdtests/a_64_bit_range_needs_no_bound_on_its_length.md -->
```click
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    views bytes[0..length];
    ensures result == bytes[index];
}
```
Top-level verification gets its resource context from the function's resource
verbs, while function calls apply the callee's verified contract as one opaque
execution step.

### Uninitialized owned memory

A plain memory clause holds initialized bytes. `owns p[a..b]`, `views
p[a..b]`, and `consumes p[a..b]` let the callee read the range, so its proof
starts with every byte initialized, and a call is refused unless the caller
has initialized every byte that holds a value
(`mdtests/an_owning_call_refuses_an_unwritten_local.md`). Storage with no
initialization history, such as the caller's own input ranges, is
initialized by its own contract. A byte counts when a store wrote it or a fact
such as a callee's `ensures defined(p[k])` covers it. Padding holds no value:
a field's clause needs only the field's bytes, and a whole object `*s` only
its fields' (`mdtests/a_struct_viewed_whole_needs_only_its_fields_initialized.md`).
A range whose length is known only at the call needs every byte from its start
to the end of a constant-size object written. A constructor's clauses on the
object it constructs are exempt, since it runs on raw storage, and so is the
source of `memcpy`, which carries each byte's initialization across.

`produces p[a..b]` hands the caller initialized bytes, so the function's proof
is refused at a return that leaves a byte of it unwritten
(`mdtests/produces_refuses_memory_the_function_did_not_write.md`), and after
the call the caller holds them written. A symbolic byte output also yields
`defined(dst[i])` at the call's return when `i` is in the produced range
(`mdtests/solve_proves_a_byte_defined_in_a_symbolic_produced_range.md`).
An initializer consumes
`uninitialized(p[a..b])` and produces `p[a..b]`
(`mdtests/an_initializer_produces_the_memory_it_initialized.md`).

`owns uninitialized(p[a..b])` holds the range with no claim that its bytes are
initialized: the callee may write them, and may not read one it has not
written. The resource is ordinary ownership of the range; only the
initialization claim differs. The proof starts with the bytes unwritten, as a
fresh local's are, so a read needs a store before it or `defined` evidence
(`mdtests/owns_uninitialized_refuses_a_read_before_a_write.md`,
`mdtests/owns_uninitialized_with_a_symbolic_length_refuses_a_read.md`).
A callee states the bytes it initialized with `ensures defined(...)`, and the
caller may read those after the call; owning a range never says by itself
that the callee wrote it.

<!-- verified-example: mdtests/owns_uninitialized_reads_what_it_wrote.md -->
```click
int32 set_then_get(int32* p) {
    owns uninitialized(p[0..1]);
    ensures result == 1;
    ensures p[0] == 1;
    ensures defined(p[0]);
}
```

`produces uninitialized(result[0..n])` returns bytes the caller then holds
unwritten, as it holds fresh `malloc` storage
(`mdtests/produces_uninitialized_reaches_the_caller_unwritten.md`).
`consumes uninitialized(p[a..b])` takes a range whatever its bytes hold, such
as a destination a loop fills before anything reads it
(`mdtests/uninitialized_destination_beside_a_viewed_source.md`).
A viewed range is only read, so `views uninitialized(...)` is refused
(`mdtests/views_uninitialized_is_refused.md`), and only a function contract's
`owns`, `consumes`, and `produces` clauses accept the form. The generated
`snprintf` contracts, and `memcpy` and `memset` in `click::c::string`, own
their destination as `uninitialized(...)`.

A range with a symbolic length, or 64-bit bounds, is marked from its first
byte onward. Another array parameter's memory is not in it: a read belongs to
the range only through an address built from its base. Memory the contract
holds initialized past the range through that same base then also needs a
store or `defined` evidence before a read.

These memory resource facts belong to the built-in memory family. The family
defines how resources entail, split, rejoin, transfer, and consume each other.
This keeps the user-facing memory syntax concrete while sharing the same
context machinery with non-memory resources.

Click also supports exact-match abstract resources:

<!-- verified-example: mdtests/token_resource_borrow_return.md -->
```click
abstract resource open_fd(fd: int32);
```

An abstract resource has no locally visible body and must use the explicit
`abstract resource` syntax. After declaration, `owns open_fd(fd)`,
`views open_fd(fd)`, `consumes open_fd(fd)`, and `produces open_fd(fd)` use the
same resource context. Arguments are type checked. Repeated equal owned units
form a quantity; a requirement for two units cannot be satisfied by one.
The function-level clause `constructs open_fd(result);` authorizes creating
one owned abstract token without consuming an input resource. At a normal
return, Click can automatically construct a missing token directly owed by
`produces open_fd(result);` when the two clauses denote the same token.
Write `fold(open_fd(result));` to create an intermediate token, for
example before folding it into a composite resource.

An abstract resource may declare fields, and nothing else:
`abstract resource obj(p: int32*) { field size: int32; }`. Its instances are
named and carry their fields, as a declared resource's do, but it has no body:
no proof folds, unfolds, or observes one. Only a contract produces or consumes
an instance, so its fields are what the contracts that move it say
(`mdtests/abstract_resource_fields_pass_through_calls.md`,
`mdtests/abstract_resource_fields_cannot_be_folded.md`). A trusted `extern`
contract can turn memory into such an instance and back, and a function that
holds one sees only its fields.

<!-- verified-example: mdtests/abstract_resource_fields_pass_through_calls.md -->
```click
abstract resource obj(p: int32*) {
    field size: int32;
}
extern void pack(int32* p) {
    consumes p[0..1];
    produces o: obj(p);
    ensures o.size == old(p[0]);
}
```

Repeated owned clauses denote a quantity rather than a duplicate-ownership
error. Omitting a coefficient transfers one unit. An owned user-declared
token may instead transfer an `int32` quantity explicitly:

<!-- verified-example: mdtests/symbolic_token_quantity_contracts.md -->
```click
owns amount of permit();
consumes amount of permit();
```

The coefficient must be provably nonnegative at the contract's point. Zero is
the resource identity and grants no authority. Symbolic coefficients are not
accepted on memory, allocation, or recursively defined composite resources.

### Populations

A family whose units are counted is declared `authorized`. Its members carry
no body of their own; the population is governed by an exclusive
`authority(...)` resource, usually owned by an ordinary control resource that
relates the count to C state:

<!-- verified-example: mdtests/counted_resource_refcount_transitions.md -->
```click
authorized resource object_ref(obj: struct object*) {}

resource object_control(obj: struct object*) {
    owns obj->refs;
    owns authority(object_ref(obj));
    fact obj->refs == count(object_ref(obj));
}
```

`count(object_ref(obj))` is an `int32` expression naming the population size.
It may name only an `authorized` family, and it observes the population only
where that family's authority is owned, as in the control's facts above. A
wildcard argument sums matching exact populations, so
`count(pool_object(pool, _))` counts every member belonging to `pool`.
`authority(...)` likewise names only an `authorized` family. Fields do not
decide whether a family can be counted: a family with fields has separately
named members rather than quantities.

Members are created and destroyed only under the authority.
`fold(object_ref(obj))` creates one member and `unfold(object_ref(obj))`
destroys one, each while the authority is owned, typically inside
`with(object_control(obj)) { ... }`. Closing the block proves the control's
facts again, so a retain must update the stored count in the same scope:

<!-- verified-example: mdtests/counted_resource_refcount_transitions.md -->
```click
struct object* object_retain(struct object* obj) {
    requires count(object_ref(obj)) < 2147483647;
    owns object_control(obj);
    owns object_ref(obj);
    produces object_ref(obj);

    ensures result == obj;
} by {
    with(object_control(obj)) {
        step();
        fold(object_ref(obj));
    }
}
```

A contract's net transfer of members is checked against the same facts:
`produces object_ref(obj)` is a one-member retain and `consumes object_ref(obj)`
a one-member release, so these clauses cannot mint or drop a member without
the corresponding counter update.

`fold(authority(object_ref(obj)))` establishes an empty population and
`unfold(authority(object_ref(obj)))` retires one whose count is zero
(`mdtests/authority_count_after_cleanup.md`; the lifecycle of a heap
reference count is `examples/refcount/`). A call inside a `with` block does
not assume the control's facts on return: closing the block proves them from
what the caller knows
(`mdtests/call_inside_open_population_does_not_assume_its_body.md`).

Every other family keeps its ordinary definition law: `fold` consumes the
body's resources and `unfold` exposes them, with no population accounting.
`docs/concepts/resources.md` describes populations, controls, and worker and
mutex custody in more detail.

### Composite resources

Composite resources are declared resources with a body:

<!-- verified-example: mdtests/composite_resource_bundles_declared_resource.md -->
```click
abstract resource socket_open(fd: int32);

resource uncalled(flag: int32*) {
    owns socket_open(7);
    owns flag[0..1];
    fact flag[0] == 0;
}
```

A Click library module may declare resources too, such as `click::c::string`'s
C string `cstr_at(p, len)`. A file sees a library resource exactly
when it sees that module's predicates and functions: the module is implicit,
imported, or brought by the C program's library calls. Declaring a resource
with the name of a visible library resource is a duplicate definition. A
resource argument is typed as a predicate argument is: a `char`,
`signed char`, or `unsigned char` pointer may be passed for a `uint8*`
parameter, and a parameter of signed character pointer type passed there is
read through its byte view `p as (uint8 *)`
(`mdtests/cstr_at_borrows_a_char_string_from_the_library.md`).

A resource may declare pure fields before its body clauses:

<!-- verified-example: mdtests/resource_fields.md -->
```click
resource buffer(p: int32*, capacity: int32) {
    field contents: List<int32>;
    field mark: Mark;
    field revision: int32;
    owns p[0..capacity];
}
```

Here `Mark` is the enum declared in the linked fixture. Fields have Click
types: supported unqualified C scalar/pointer types or algebraic types,
including instantiated generic types. Field names must be distinct from one
another, resource parameters, and body witnesses. Fields precede any guard
and cannot be declared inside it. Qualified C types, struct types/pointers,
arrays, and function-pointer field types are not supported.

Resources with fields are intended for exclusive instance-based ownership:
each member is a separately named instance, so quantities such as
`1 of resource(...)` are rejected. Fields do not decide whether a family can be
counted; `count(resource(...))` is admitted exactly when the family is declared
`authorized resource`, with or without fields. Named ownership binds an
exclusive instance with arbitrary typed fields:

<!-- verified-example: mdtests/resource_instance_bindings.md -->
```click
int32 identity(int32 value) {
    owns cell: marked_cell();
    ensures result == value;
    ensures cell.model == old(cell.model);
    ensures cell.revision == old(cell.revision);
}
```

Here `marked_cell` is declared in the linked fixture. `cell.model` reads the
currently owned instance's field; `old(cell.model)` reads its function-entry
state. Returning ownership does not itself promise unchanged fields; use an
explicit postcondition. Instance identity is distinct from field state, and
fields are symbolic Click values, not executable C ghost parameters.

Explicit callback applications such as
`step(Read, { cell: first })` transport ownership with fresh post-call fields constrained
by the selected contract. `unfold(cell)` exposes an instance's immediate memory
body and its facts; field names in the body denote that instance's fields.
For witness-free memory-only bodies, including guarded and matched bodies, unfolding consumes the named
instance without retaining an open handle. Current field projections require
owned instances; entry reads such as `old(cell.value)` remain available.
The `fold(cell)` form uses the instance's entry-state fields as its
target, and checks the complete body ownership and facts. It does not require
an earlier unfold.

An explicit fold binds its result and supplies every field by name:

<!-- verified-example: mdtests/resource_cell_construction.md -->
```click
void init(int32* p, int32 value) {
    consumes p[0..1];
    produces c: cell(p);
    ensures c.value == value;
} by {
    step_until(function.exit);
    let c = fold(cell(p), { value: value });
    close();
}
```

Here `cell` is declared in the fixture. The fold consumes its body ownership
and checks the body facts with the proposed fields. No earlier resource is
required. Rebinding a contract's resource name also permits changed fields
after C updates the memory; the name must not currently own another instance.
Field order is irrelevant, but missing, duplicate, unknown, or ill-typed
fields are rejected. Initializers accept C-valued and ADT-valued symbolic
expressions, including constructors, `old(c.model)`, matches, and pure-function
applications. For example:

<!-- verified-example: mdtests/resource_adt_construction.md -->
```click
let c = fold(cell(p), { model: Mark::Set(value) });
```

The complete declaration and proof are in `mdtests/resource_adt_construction.md`.
Pure-function applications remain symbolic;
fold checks the resource relation against the proposed value. Initializer
memory reads must be justified. A consumed name does not supply a current
field value; use an entry read, `old(...)`, when that is the intended model.
An ordinary C call transports constructed resources through the explicit
binder map described under "Calls that transport named instances".

A C-typed field is stable model data while its instance is folded, so the
body may use it wherever it may use a C expression over the parameters: as a
memory-range endpoint, and as a child's argument. Folding takes the endpoint
from the proposed field value and checks the body facts against it; unfolding
publishes the range at the folded field's value:

<!-- verified-example: mdtests/resource_field_memory_endpoint.md -->
```click
resource zero_suffix(data: int32*, capacity: int32) {
    field start: int32;
    owns data[start..capacity];
    fact 0 <= start;
    fact start <= capacity;
    fact forall (k: int32) {
        start <= k and k < capacity implies data[k] == 0
    };
}
```

`let after = fold(zero_suffix(data, capacity), { start: old(before.start) + 1 })`
refolds the suffix one cell later, leaving the first cell with the caller. A
field of an algebraic or `Integer` type has no C value and cannot select a
range; match it and use a C-typed constructor binding instead. The negative regressions are
`mdtests/resource_field_memory_endpoint_rejects_out_of_bounds_fold.md` and
`mdtests/resource_field_memory_endpoint_unfold_rejects_other_endpoint.md`.

In a contract, a folded field-bearing instance whose body is unconditional and
unmatched makes the cells its body owns readable to the contract's other
resource clauses, as a folded field-free composite does:
`consumes freed: arena_prefix_region(region);` beside
`consumes before: arena_prefix_state(region->arena);` reads `region->arena`
through the `*region` the region's body owns, in either clause order.
The same holds for the clauses the contract returns and for the cells its
postconditions read inside its folded instances
(`mdtests/contract_returns_field_bearing_sibling.md`,
`mdtests/borrowed_instance_argument_reads_old_field.md`).
The cells are views only: writing one still needs an explicit `unfold`, and a
cell the body does not own stays unreadable
(`mdtests/contract_field_bearing_instance_views_grant_no_write.md`,
`mdtests/contract_field_bearing_instance_views_only_owned_cells.md`).

An open instance keeps its captured fields available by their ordinary names.
After `unfold(before)`, `before.prefix` reads the captured prefix. A loop
invariant can use `old(before.prefix)` to read it at loop entry.
The unfold pattern can give a C-typed field a separate proof name:

<!-- verified-example: mdtests/resource_unfold_binds_scalar_field.md -->
```click
let { prefix: p } = unfold(before);
```

`p` is a plain proof value for the rest of the function. Later `have`s, loop
invariants and `decreases` measures, fold input maps such as
`fold(claimed_prefix(data, occupied, capacity), { prefix: p + 1 })`, and the
closing contract claims may all name it. One pattern may mix child slots and
fields, `let { marks: m, prefix: p, free: f, live: n } = unfold(state)`
(`mdtests/resource_unfold_binds_children_and_fields.md`). A binder must be a
fresh name that is not a C parameter or local in scope. Only C-typed fields
bind this way; an algebraic or `Integer` field is refused. For an algebraic
field, a proof `match` before the unfold names its constructor payloads.
Expansion and audit print
the pattern as written. See the dotted form in
`mdtests/resource_unfold_reads_the_opened_field.md`.

A fold can also consume an instance as a child of its result. Reading that
child's field afterward does not imply that the child was unfolded. If the
held parent's model contains the child's model as a constructor payload,
match the parent before a loop and keep the payload in a proof binding for
the invariant. This keeps a name for the value without opening either
instance (`mdtests/loop_invariant_binds_model_from_a_folded_parent.md`).
The refusal distinguishes this fold from an unfold and does not suggest an
unfold-pattern binding for an algebraic field.

Guarded and constructor-matched memory-only bodies support explicit construction
and field updates with the same `let c = fold(...)` syntax. No earlier unfold
is required. Guarded bodies support the
existing single `if` guard with an empty false case. Fold/unfold requires proof
of the selected guard case. The false case exposes no memory or body facts;
unfold consumes the instance in either case. A fold checks the guard with the
proposed fields and must justify the selected body's ownership and facts.
Post-return folds are checked separately against each return path's memory,
ownership, and guard assumptions. Every returning path must restore the
ownership promised by the contract; a sibling's fold cannot supply it.
The regression is `mdtests/resource_fields_guarded_memory_body.md`.

A field-bearing body may instead match one algebraic field:

<!-- verified-example: mdtests/resource_fields_match_memory_body.md -->
```click
resource cell(p: int32*) {
    field model: Maybe<int32>;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => {
            owns p[0..1];
            fact p[0] == value;
        },
    }
}
```

Here `Maybe<T>` is declared in the linked fixture. Arms must cover every
constructor exactly once. Bindings are scoped to their arm and have the
constructor's instantiated types, including pointers and nested ADTs. A
binding whose constructor field is declared `struct tag*` is a struct base for
the whole arm: `parent->left` names that field's cell at its declared offset
and width in `owns`, in `fact`, and in a child instance's arguments. The
datatype may be declared above or below the resource, because declaration
order does not create scope. A binding of any other type is not a base, and
using one as one is refused with the type the constructor declares. They
cannot shadow resource parameters or fields.

A pointer-typed payload is an ordinary C pointer value, so a proposition may
compare it with any C pointer expression, in `requires`, `ensures`, `have`,
`rewrite`, and `normalize() using`. A resource arm that records the owner's
own address, `fact p == identity`, is what connects the two: the C tests an
address, the model tests its payload, and that fact is the bridge. Pointers
stay pointers; there is no conversion to an integer and the payload carries no
ownership. The regression is
`mdtests/model_identity_pointer_payload.md`, with
`mdtests/model_identity_pointer_payload_rejects_other_cell.md` as its negative.
A pure function may return a pointer type. Its opaque application retains the
function and argument values until checked unfolding; equality rewriting can
enter those arguments. Shared equality closure also establishes equal results
from equal typed arguments, including model aliases and nested pointer calls.
Argument order, scalar types, and array-reference version points remain distinct;
result equality does not imply argument equality. See
`mdtests/pure_pointer_call_congruence.md` and its missing-argument-equality negative.
The result has the declared pointer type and grants no
ownership or separation from another pointer. See `mdtests/pure_pointer_result.md`
and its unequal-pointer, distinct-call, and unowned-read negatives.

Resource fold/unfold requires constructor evidence for the actual instance field (for example,
`c.model == Maybe<int32>::Some(expected)`); an unknown field does not cause
implicit proof-by-cases. Only the selected arm's memory and facts are exposed.

A contract section selects an arm as well, before any proof step runs. When the
section's requirements together with constructor exhaustiveness leave exactly
one arm possible, lowering exposes that arm's cells as read authority while the
instance stays folded, so another requirement or resource clause of the same
contract can read through it:

<!-- verified-example: mdtests/resource_match_arm_selected_at_contract.md -->
```click
owns c: cell(node);
requires c.model != Maybe::None;
requires node->value >= 0;
```

`c.model != Maybe::None` selects `Some` because `Maybe` has two constructors,
and `exists (v: int32) { c.model == Maybe::Some(v) }` selects it directly. A
disequality against a constructor that carries fields rules nothing out:
`c.model != Maybe::Some(3)` still leaves `Some` possible. If no single arm is
entailed the instance stays folded and the read is refused with a diagnostic
naming the instance and the field whose arm nothing selects; there is no
implicit proof by cases. Selection grants read authority only — ownership moves
only through an explicit `unfold` — and it does not expose contained child
instances. A loop head decides the same way, with its invariants in the part
the requirements play; a proof that needs the constructor itself, to `unfold`
or to name children, writes an explicit proof `match` on the model, which runs
at any frontier including a loop's `maintain` body
(`mdtests/loop_body_proof_match.md`). The regressions are
`mdtests/resource_match_arm_selected_at_contract.md`,
`mdtests/resource_match_arm_selected_by_existential.md`, and
`mdtests/resource_match_arm_needs_one_entailed_arm.md`.
An explicit fold selects the arm from its proposed model, so an update can
change constructors when the new arm's ownership and facts are established.
The regression is `mdtests/resource_conditional_construction.md`.
The same ownership and path-local return checks apply.
Match arms can also expose named, directly recursive child instances:

<!-- verified-example: mdtests/resource_recursive_children.md -->
```click
resource tree(p: int32*) {
    field model: Tree;
    match model {
        Tree::Leaf(value) => { owns p[0..1]; fact p[0] == value; },
        Tree::Branch(value, lp, lm, rp, rm) => {
            owns p[0..1];
            owns left: tree(lp);
            owns right: tree(rp);
            fact p[0] == value;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}
```

Here `Tree` is declared in the fixture. Give the exposed children independent
names, then pass their owned instances explicitly when constructing a parent:

<!-- verified-example: mdtests/resource_independent_children.md -->
```click
let { left: l, right: r } = unfold(root);
unfold(l);
step_until(function.exit);
let l = fold(tree(left), { model: Tree::Leaf(2) });
let root = fold(tree(p), { model: old(root.model), left: l, right: r });
```

`let { ... } = unfold(root)` consumes `root`, exposes its immediate memory,
and introduces folded children. It is the one form that names what an unfold
opens; the trailing `unfold(root) as { ... }` form is refused with that
advice (`mdtests/unfold_names_its_pieces_on_the_left.md`). No parent handle or `root.left` path remains.
Child-field equations and the aliases they establish are local to each match
arm; another arm may reuse the child name with different parent fields.
Each selected-arm child must be named exactly once. An introduced name must
not already own a resource. `unfold(l)` exposes the child's immediate body;
an arm with no children needs no bindings (an empty output pattern is also
accepted).

Owned child indices also accept typed C-valued pure calls. For example,
`owns left: metadata_at(identity(left_model));` obtains its C pointer from
logical model data. The ordinary pure-expression evaluator supplies the
value; the fold/unfold checker still checks the child parameter type and
requires every read and safety obligation to be established. A pure call
returning an algebraic or mathematical value cannot serve as a C index.
See `mdtests/resource_child_pure_arguments.md` and
`mdtests/resource_child_pure_arguments_recursive.md`.

The fold input map accepts field initializers and child bindings in either order.
A field key takes a value expression. A child slot takes the name of a held
resource. Folding consumes the selected children and the parent's immediate
memory, checking each child's family, arguments, and fields against the proposed
model. Missing, duplicate, unfolded, or mismatched children are rejected.

Supply each named child of the selected arm in the input map, even if its
held instance has the same name as the slot. Omit the map when it has no
entries.

<!-- verified-example: mdtests/a_fold_binds_same_named_children_explicitly.md -->
```click
let { left: left, right: right } = unfold(root);
unfold(left);
step_until(function.exit);
let left = fold(tree(lp), { model: Tree::Leaf(2) });
let root = fold(tree(p), { model: old(root.model), left: left, right: right });
```

A resource that declares no `field` may still name a child that has fields,
and state facts about them:

<!-- verified-example: mdtests/a_hidden_record_resource_is_held_without_a_name.md -->
```click
resource pair(p: struct pair*) {
    owns p->a;
    owns p->n;
    owns first: counted(p->a);
    fact p->n == first.v;
    fact first.v >= 0;
}
```

It keeps the child's fields in a record the author does not write, so their
values survive a fold as a declared field's do. The child must be declared
before it. It may be held without an instance name, `owns pair(p);`, unfolded with `let { first: c } = unfold(pair(p));`,
and folded with `fold(pair(p), { first: c });`, which takes only the child
input. With the child bound to `first`, write `fold(pair(p), { first: first });`
(`mdtests/a_hidden_record_folds_an_explicit_same_named_child.md`). The parent
may also be held by name, `owns x: pair(p);`.

The retained child fields have structural paths. `pair(p).first.v` selects
`first.v` in the one in-scope instance with the exact written target `pair(p)`.
No equality or alias search selects the instance. If several instances have
that target, use a named instance, such as `whole.first.v`. Selecting the field
does not unfold the parent or grant ownership of the child's memory.
`old(pair(p).first.v)` names its entry value after unfolding; the current path
requires the parent to be held at the selected state. The call form currently
selects ordinary resource applications without type or resource arguments.

<!-- verified-example: mdtests/nested_resource_fields_have_a_call_spelling.md -->
```click
have pair(p).first.v == old(pair(p).first.v);
let { first: c } = unfold(pair(p));
have c.v == old(pair(p).first.v);
```

The record initializer has no source syntax, but diagnostics and expansion show it. A
refusal lists a held instance with its record,
`owns pair(p) record { first.v: <unnamed A> }`, using the same placeholders
as the pure facts beside it
(`mdtests/a_hidden_record_is_shown_beside_its_resource.md`). A refused fold
adds `proposed fold: pair(p) record { ... }` below its failed body fact
(`mdtests/a_refused_fold_shows_the_hidden_record_it_proposed.md`).
`click expand` writes the record a fold sets as a trailing comment, which the
parser ignores: `fold(pair(p), { first: c }); // record { first.v: c.v }`.

A resource that declares fields of its own says where a named child's field
is kept with one equation,
`fact first.v == first_v;`. After it, `first.v` in the body reads that
parent field, so later facts may mention it; a fact that reads `first.v`
before the equation is refused with the equation to write.

<!-- verified-example: mdtests/a_parent_with_fields_states_facts_about_a_childs_field.md -->
```click
resource pair(p: struct pair*) {
    field first_v: int32;
    owns p->a;
    owns p->n;
    owns first: counted(p->a);
    fact first.v == first_v;
    fact p->n == first.v;
}
```

The new parent need not have existed before; `consumes l: tree(left);` names
an input child without promising to return it separately.

Parent-qualified resource handles such as `root.left` are not supported.
Unfolding a recursive body requires `let { ... } = unfold(...)` to name its
selected children. Refolding supplies the selected child slots in the input
map. Unfold consumes the parent, so it
cannot be projected or unfolded again unless a new owned parent is constructed.

A child names one declared field-bearing resource: the parent's own definition
or another one. Its arguments and field equations are checked against that
definition, so a child of another family carries that family's fields:

<!-- verified-example: mdtests/resource_child_of_another_family.md -->
```click
resource ctx_at(node: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Left(up_node, value, right_model, up_model) => {
            owns node->value;
            owns node->left;
            owns node->right;
            owns right: tree_at(node->right);
            owns up: ctx_at(up_node);
            fact node != 0;
            fact node->value == value;
            fact right.model == right_model;
            fact up.model == up_model;
        },
    }
}
```

Here `ctx_at` owns a `tree_at`, and `tree_at` never owns a `ctx_at`; two
definitions that own each other are still rejected as a composite resource
cycle. `Context::Top => {}` shows that an arm may own nothing at all, and
`fold(ctx_at(node), { model: Context::Top })` constructs it.

An arm need not own only cells of the resource's own parameters. The frame
below is keyed by the focused child and owns the cells of the `parent` the
constructor carries, including the sibling subtree reached through it:

<!-- verified-example: mdtests/resource_arm_binding_struct_base.md -->
```click
resource ctx_at(child: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Left(parent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns sibling: tree_at(parent->right);
            owns up: ctx_at(parent);
            fact parent != 0;
            fact parent->left == child;
            fact parent->value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}
```

`Context::Left`'s first field is declared `struct tree_node*`, so `parent`
carries that layout for the arm. After `let { sibling: s, up: u } = unfold(ctx)`
the arm's facts hold of the exposed cells, so `fact parent->left == child`
is what lets a proof read the focused node back out of the frame.

Equations for all child fields must bind each of them to an immediate
constructor field or to a field of the parent itself, of the matching type.
In particular, a child of the parent's own family strictly descends to a
proper submodel, so its model field must be a constructor field.
Child arguments may be read-only C expressions, including stored pointer
fields such as `p->left` and C-typed fields of the parent.

A body without a `match` may name children too, provided the parent has
fields and each child is of another family. Its children's fields are then
equations with the parent's fields:

<!-- verified-example: mdtests/resource_unfold_binds_children_and_fields.md -->
```click
resource arena_prefix_state(arena: struct arena*) {
    field prefix: int32;
    field live: int32;
    owns arena->data;
    owns arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    owns marks: occupied_marks(arena->occupied, prefix);
    owns free: free_suffix(arena->data, arena->capacity);
    fact marks.count == live;
    fact free.start == prefix;
    fact arena->live_regions == live;
}
```

`unfold(state)` exposes children at `state.marks` and `state.free`.
`fold(state)` takes those same children back. To name them independently,
use `let { marks: m, free: f } = unfold(state)`. To select inputs explicitly,
use `fold(arena_prefix_state(arena), { ..., marks: m, free: f })`.
A body or arm may also own a field-free declared
resource without a name, `owns cell_value(cell);`; it stays folded while the
parent is unfolded (`mdtests/resource_match_arm_unnamed_child.md`). A
field-bearing resource owned in a body needs a child name. Loads must be readable from the immediate body's
owned memory, not from a still-folded child or unrelated ambient ownership.
Fold checks this memory before interpreting the child arguments. Expression
safety and path premises must be proved; argument evaluation does not split
the proof into cases. See `mdtests/resource_tree_node_init.md`.
Memory and token families in a child slot, witnesses, nested resource
matches/guards, arbitrary match scrutinees, and passing child paths as
contract arguments remain unsupported. No operation automatically unfolds an entire recursive structure.

A declaration alone grants no ownership, and binding an instance does not
implicitly expose its memory body.

A composite body may instead have one top-level guard:

<!-- verified-example: mdtests/recursive_conditional_resource.md -->
```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        owns list(node->next);
    }
}
```

A body may also bind an existential pointer with `let name: type where
proposition;`. The witness is in scope for every later clause, and the `where`
proposition is one of the body's pure facts:

<!-- verified-example: mdtests/resource_witness_unfold_fold.md -->
```click
resource packed(node: struct node*) {
    owns *node;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}
```

This is how a resource describes a pointer packed into an integer word, such
as a tail pointer with a mark bit or an `rb_node` parent with its color. The
witness needs no syntax at `fold` or `unfold`. Unfolding binds it to a fresh
symbolic pointer constrained by the `where` fact, and the program's own cast
`(node->word & ~1) as (struct node *)` then recovers exactly that pointer. Folding
binds it to the recorded origin of the word the `where` fact relates it to, so
after `node->word = (unsigned long)tail;` the witness is `tail`. A word with no
recorded origin cannot fold, and the diagnostic names the missing body fact.

A resource parameter serves the same purpose when the packed pointer is already
named by the caller. `rb_at(p, parent)` in
`mdtests/rb_ascent_parent_link_guard.md` takes
the parent as its second parameter and states
`fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);`,
so `rb_parent`'s `(r->__rb_parent_color & ~3) as (struct rb_node *)` recovers that
parameter with its provenance. Keep the tag in the stated form
`(p->__rb_parent_color & 1)` rather than an opaque pure-function application:
clearing tag bits needs the tag proven below 4, and a function such as
`color_bit(color)` is opaque until it is unfolded at a concrete constructor. A
second fact `(p->__rb_parent_color & 1) == color_bit(color)` then ties the bit
to the model.

A cast fact such as `((p->__rb_parent_color & ~3) as (struct rb_node *)) == parent`
names the read of the word at the state where it was stated. The program's
cast reads the word where it executes, so after a store through another
pointer the two are different reads, and the cast no longer designates
`parent` (`mdtests/a_parent_cast_fact_is_not_carried_across_a_store_through_another_node.md`).
Restate the fact before the cast, with `close()` across plain stores or with
`transport` and the store's separation, and through a join's `ensuring`
clause when a branch lies between
(`mdtests/a_parent_cast_restated_after_a_store_lets_the_parent_be_dereferenced.md`).

Resource facts may compose nonrecursive, read-free model getters, such as
`child(child(model))`. Inspection checks the caller's argument reads and the
written getter body separately; each read-free definition is inspected once.
Nested syntax does not imply source recursion. Recursive resource-fact
inspection remains rejected, and a read hidden in a getter argument still
needs a covering owned or viewed resource. The fixtures
`resource_fact_accepts_nested_model_getters.md`,
`resource_fact_still_rejects_recursive_getters.md`, and
`resource_fact_nested_getter_argument_requires_authority.md` cover these rules.

There is no `else`: when the guard is false, the body is empty. The guard must
be load-free, because it decides which memory resource facts exist and therefore
cannot depend on reading that same memory. A guarded body may directly contain
the resource being defined. This direct self-recursion is the supported
recursive form; unguarded recursion and mutual resource cycles are rejected.

Automatic projection keeps a guarded body opaque while its guard is undecided.
Explicit `observe`, `fold`, and `unfold` require the guard to be decided.
When active, they expose or consume exactly one body layer, leaving a recursive
child such as `list(node->next)` folded. This makes proof cost depend on the
number of explicit list operations, not the unknown length of the list.

Holding the folded abstract token exposes its immediate pure facts and viewed
resource facts, but not its owned contained resource facts. Hidden contained
owned resources also expose direct `contains(...)` and `separate(...)` pure
facts. In an explicit proof script,
`observe(uncalled(flag));` non-destructively records this projection while
keeping owned contained resources hidden. `unfold(uncalled(flag));` consumes the
abstract token resource fact and exposes its contained resource facts for
mutation. Composite bodies can bundle built-in memory resources and other
declared resources. Declared `fact` clauses are pure facts.
Before `fold(uncalled(flag));`, the declared pure body facts must be exact facts
in the current proof context (or normalize to true without context). `fold`
then consumes the contained resource facts and returns the abstract token
resource fact. It does not invoke `close()`; use an explicit `have` first when a
body fact needs derivation. The end of the `by { ... }` block checks the overall
claim.

A function block may be resource-only when it consumes a resource:

<!-- verified-example: mdtests/callback_resource_complete_once.md -->
```click
int32 complete(int32 cb) {
    consumes can_complete(cb);
}
```

Resource facts are written with resource verbs:

<!-- verified-example: mdtests/resource_verbs_owns_views_consumes_produces.md -->
```click
int32 update(int32* p) {
    owns p[0..1];
}

int32 inspect(int32* p) {
    views p[0..1];
}

int32 close(int32 fd) {
    consumes open_fd(fd);
}

int32 open(int32 fd) {
    produces open_fd(fd);
}
```

`owns` means the function starts and ends with the owned resource. `views`
means the function borrows the resource for the call and reads it only.
`consumes` requires an owned resource and does not return it. `produces X`
returns an owned resource. To produce a memory view, name the input with
`views *p as source;` and write `produces view(*p) from source;`. The
input must cover the output, and the output keeps the input borrow active
until the caller gives it up. You can omit `from` when exactly one input
view has the same lowered range. See
[Producing a view](../../concepts/resources.md#producing-a-view).
A newly produced composite that contains a view names its source with
`produces cursor(...) from source;`. The source can be a `views ... as source;`
requirement or an existing borrowing composite named by `consumes ... as source;`.
`requires` and `ensures` accept pure propositions
only.

At contract entry, every memory read used to compute a resource clause must
be readable from the contract's entry resources or a `requires viewable(...)` precondition.
The contract can supply this access through an owned resource or a `views`
clause, including one declared later. For example, evaluating the argument to
`owns pair(node->left->left);` reads two pointer fields. The clauses
`views node->left;` and `views node->left->left;` supply read access to both.
If Click cannot establish access for a read during entry resource evaluation,
it reports a `contract error`.

`consumes X;` beside `produces X;` for the same `X` is exactly
`owns X;`, and the pair is refused with that one clause to write (with the
`produces` clause's proof, `owns X by proof;`;
`mdtests/consumes_and_produces_one_place_is_owns.md`,
`mdtests/consumes_and_produces_one_resource_is_owns.md`). The refusal applies
where both clauses certainly name one resource: unconditional clauses whose
place and arguments are built from parameters and constants. A place reached
through memory the function may change, such as `consumes p->data[0..1];`
with `produces p->data[0..1];` or `consumes list(node->next);` with
`produces list(node->next);`, is read at entry by `consumes` and at exit by
`produces`, can name a different object, and stays a pair. Keep the separate
verbs for one-way transfers and resource transformations.

A return-side clause is the caller's view, so its arguments are read that way.
`result` is the returned value, and a struct returned by value is read
through its fields, `produces cell(result.p)`: the caller holds the resource
at the value the field has
(`mdtests/c_produced_resource_over_returned_struct_field.md`,
`mdtests/c_produced_resource_over_returned_struct_field_is_only_that_field.md`).
A parameter means the value the caller
passed, not one the body assigned to that parameter: a returned borrow is
evaluated at entry for exactly this reason, so `owns t: tree_at(root);` names
the caller's tree however the body used `root`. A proof tactic reads its own
resource arguments at the cursor it stands on, so a body that reassigns such a
parameter has to refold the borrowed instance before that assignment; the
entry position cannot be written inside a `fold`.

A function whose result sits somewhere the caller cannot name that way says so
directly. A resource argument may be the C null pointer constant `0` at a
pointer-typed resource parameter, which is how a walk that ends at the root of
a parent-linked structure produces `ctx_at(result, 0)`: the position it
reached has no parent, and the parameter it started from is a different node.

<!-- verified-example: mdtests/loop_ascending_walk_to_root.md -->
```click
consumes c: pctx_at(node, parent);
consumes t: ptree_at(node, parent);
produces ctx: pctx_at(result, 0);
produces sub: ptree_at(result, 0);
```

A `void` function has no `result`, so a cursor it left somewhere else is named
through a cell the contract owns. A produced clause's cell reads are taken in
the exit state, so when the contract owns `root->rb_node`, `produces u:
rb_at(root->rb_node);` is the whole tree at the position the body linked, and
the caller reading that same owned cell after the call sees the same object.
This is the form for the Linux insert fixup, which returns nothing and
reassigns its `node` parameter as it climbs
(`mdtests/rb_produces_through_the_root_cell.md`). A parameter the body
reassigned cannot stand there: it means the caller's actual, and a caller
substitutes its own, so the clause would describe an object the exit does not
hold.

The same call may produce both the link cell and a named instance whose
argument reads it: `produces root->p; produces out: leaf(root->p);`.
The primitive output supplies read authority for the named output argument;
the output clauses can be written in either order. This applies to C calls
and applications of checked user tactics
(`mdtests/user_tactic_produced_cell_supplies_named_output.md`).

A produced instance is the one the body folded under that name, so a walk
hands its final instances over by refolding them under the produced names at
the arguments the exit reached. Naming a position the proof does not hold
fails by naming the missing resource
(`mdtests/loop_ascending_produces_wrong_arguments.md`).

Ownership permits both loads and stores; a view permits loads and keeps the
covered memory unchanged and allocated while the borrow is active. A callee
using `views` borrows the caller's viewed or owned element for that call. The
lent element is out of the caller's reach until the return recovers it, and no
second persistent view is created. A view that was already present in the
caller remains persistent. The entry clauses of a contract may claim ownership
of each byte at most once, including ownership inside folded resources. A
contract may not own and view the same memory. That overlap is refused at
entry and at the call. This also applies to a folded resource. An `owns`
input already supplies read access to that resource, so a contract cannot
also request a `views` input for the same resource. Owned elements are
transferred by `owns`, `consumes`, and `produces`.

Fixed-size heap objects add the built-in owned resource
`allocation(base, bytes)`. It is exclusive authority and responsibility for
one live heap lifetime; it does not authorize memory access. Complete access is
written separately with `*base`. Allocation authority cannot be
`views`-ed or duplicated, and a verified function may not silently drop it:
the authority must be returned (possibly inside a composite resource) or
consumed by an actual `free`.

A callee can consume `allocation(p, bytes)` and produce
`allocation(result, bytes)` with `ensures result == p`. This returns the same
live allocation and its cleanup obligation through the result alias; it does
not create a new lifetime. Freeing that alias invalidates both pointer spellings
([checked example](https://github.com/clicklang/click/blob/master/mdtests/returned_allocation_pass_through_keeps_cleanup_authority.md)).

<!-- verified-example: mdtests/conditional_resource_branchless_free.md -->
```click
resource owned_item(item: struct item*) {
    if item != 0 {
        owns allocation(item, sizeof(struct item));
        owns *item;
    }
}
```

The conditional body gives a nullable factory one uniform result resource.
The condition must be a well-typed proposition over values in scope. It may
remain symbolic when the resource is declared. The proof checks the resource
obligations for the alternatives that can occur.
On the null branch the body is empty. On the success branch it packages both
access and lifetime authority. A read-only helper can `views owned_item(item)`
without gaining the ability to free it; a destructor must consume and unfold
the owned wrapper before calling `free`. Once a read-only helper returns, that
call-scoped borrow is over, so the caller may immediately pass its retained
owned wrapper to the destructor. Conversely, an independently held direct or
composite view of the same allocation remains live and makes `free` fail at the
deallocation statement; views proved separate survive.

When the guard is not known at function entry, a proof-level `if` can split on
it even if the C body is branchless. Each proof case unfolds the matching
resource body: the empty branch certifies operations such as `free(NULL)`, and
the active branch exposes the resources those operations consume. Exact
contract certification checks both cases independently, so this does not add
a precondition or require rewriting the C control flow. The same condition
guards the mutable footprint inferred from the resource. At an opaque call,
Click decides the guard before evaluating its pointer and range expressions;
an inactive body therefore contributes no footprint.

A loop may free storage and continue. The ordinary iterative release unfolds
the node its binder holds, frees it, and moves to the next one; the back edge
returns the rest of the list in the binder, and the freed node's tombstone is
the only heap difference from the loop head
(`mdtests/loop_frees_one_list_node_per_iteration.md`). A tombstone is a
double-free and stale-pointer diagnostic, not authority: what the back edge
must return is ownership, so freeing storage the head held live, or freeing
the same allocation on two iterations, is still refused by the ownership join
(`mdtests/loop_heap_lifetime_join.md`), and a pointer kept to a node an earlier
iteration freed cannot be read through
(`mdtests/loop_reads_a_node_freed_in_an_earlier_iteration_is_refused.md`).

Composite and token arguments are compared using proved scalar and pointer
equalities. Thus a held `list(node->next)` can satisfy `list(tail)` after the
proof establishes `node->next == tail`; the resource does not depend on one
particular syntactic form of that pointer.

A call can pass a covered subrange, such as consuming `p[0..1]` from a caller
that owns `p[0..2]`; Click keeps the residue and rejoins adjacent returned
ranges. The same applies to symbolic ranges when the current facts prove the
subrange is covered. Two held ranges are adjacent when one ends where the
other starts as written or by an exact equality premise, so `p[0..n]` and
`p[m..4]` under `n == m` rejoin into `p[0..4]`; a gap between them is never
bridged (`mdtests/fold_joins_ranges_abutting_by_proved_equality.md`,
`mdtests/fold_join_needs_the_endpoint_equality.md`). A range held over a
displaced base, such as the `owns (x + i)[0..1]` a call on `x + i` returns, is
compared in the coordinates of the base it sits an exact number of elements
from, so it rejoins `x[0..i]` and `x[i + 1..4]`
(`mdtests/interior_pointer_pieces_rejoin_after_an_external_call.md`,
`mdtests/owned_pieces_that_may_not_abut_do_not_rejoin.md`). Viewed and owned memory elements also make the covered
range viewable for symbolic execution, so ordinary external reads and writes
do not need a separate `viewable(...)` requirement for the same range.

This is intentionally not a complete resource system. Memory permissions have
no fractional form, and there are no general ownership predicates, general
allocator APIs, or user-defined resource algebras. Exact struct allocation and
runtime-sized `int32` arrays are the
supported heap slices. `viewable` remains a separate concept from memory
permission: viewability proves an access is in bounds, while memory resources
authorize the access.

### Iterated guarded ownership

A resource body may own one element range per index of a bounded range, held
exactly when a guard cell the same body owns says so:

<!-- verified-example: mdtests/iterated_ownership_declaration.md -->
```click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}
```

The clause reads: for every `k` with `0 <= k < capacity`, if `occupied[k] ==
0`, the body owns `data[k..k + 1]`. It is one resource fact, never a list of
`capacity` facts, and nothing enumerates the range: unfolding `arena_cells`
exposes the owned guard cells and the one iterated fact, folding consumes
them, and every question about one element reads that element's guard cell.

The declaration is checked once:

- the `where` proposition must be `lo <= k and k < hi` (in any of the
  equivalent comparison forms) with bounds that do not mention `k`;
- the guard must be `g[k] == v` or `g[k] != v` over `int32` cells, and every
  guard cell must be owned by the same body, so no one else can change it
  while the resource is folded
  (`mdtests/iterated_ownership_rejects_unowned_guard.md`);
- the element must be `base[s * k + a..s * k + b]` with integer constants
  and `0 < b - a <= s`, so no two indices share a cell; `data[k..k + 2]` is
  refused with the stride that would fix it
  (`mdtests/iterated_ownership_rejects_overlapping_elements.md`);
- a body declares at most one iterated clause, and match arms declare none.

Without an `if`, the clause owns every element; it must then be the
one-cell element `base[k..k + 1]`, and it is exactly the range `owns
base[lo..hi]` and lowers to it.

Once the resource is open, `unfold(arena_cells(data, occupied, capacity)[i]);`
exposes just the element at `i`. The iterated clause supplies its memory
range. `fold(arena_cells(data, occupied, capacity)[i]);` restores that element.
Both require its guard to hold. The resource arguments select the exact
held clause. If C has reassigned an argument, an explicit point can select
the old arguments, as in
`fold(at(opened, arena_cells(data, occupied, capacity))[i]);`.
The index and guard are still read in the current state.
See `mdtests/indexed_iterated_ownership.md`.

The `[..]` selector converts the whole iterated clause.

- `fold(arena_cells(data, occupied, capacity)[..]);` forms the clause from
  its covering range when every guard is true, or from no element memory when
  every guard is false.
- `unfold(arena_cells(data, occupied, capacity)[..]);` consumes the clause
  with all slots restored and returns the covering range when every guard
  is true.

The guard is read against the current cells, so a C store to a guard cell
changes which elements the fact claims. Such a store is allowed only at an
index where the fact claims nothing: an index out of range, an index taken
out, an index whose guard is known false, or an index whose element this
context owns outright. After the store the slot stays open until indexed `fold`
restores its element, unless the stored value makes the guard false. So the
allocation protocol is indexed `unfold` then mark
(`mdtests/iterated_ownership_allocate_one.md`), the free protocol is clear
then indexed `fold` (`mdtests/iterated_ownership_release_one.md`), and marking a
cell the fact still holds is refused
(`mdtests/iterated_ownership_rejects_guard_store_while_held.md`). A fold of
the declaring resource requires the fact with nothing taken out, so it
holds exactly the elements whose guard is true
(`mdtests/iterated_ownership_rejects_fold_with_element_out.md`). A write
to guard cells that does not pass through a C store, such as a call's
effect, drops the fact instead.

The fact itself grants no access: a store to `data[j]` needs the element
taken out first (`mdtests/iterated_ownership_rejects_store_with_closed_slot.md`).
A loop takes one element per iteration from a fact inside its own resource
(`mdtests/iterated_ownership_claim_loop.md`,
`mdtests/iterated_ownership_release_loop.md`), and freed cells are reused by
a larger run with no merge step
(`mdtests/iterated_ownership_released_cells_feed_an_external_claim.md`).
The design record is in [the resource tracker's internals
page](../../internals/resource-tracker.md#iterated-guarded-ownership).

### Calls that transport named instances

A C function whose sidecar declares instance binders is called with an
explicit map from each of those binders to an instance the caller owns:

<!-- verified-example: mdtests/c_call_binder_transport.md -->
```click
step(increment, { first: c });
```

The first argument is the call as written in the source, so the step still
selects one call statement: the frontier must be a call to that function with
that many arguments. A callee with no `owns`, `consumes`, or `produces`
binder takes no map. Duplicate, unknown, wrong-family, and unowned entries
are rejected where they are written.

A binder the map leaves out, or every binder when the call is run by a bare
`step()` or by the implicit tail, is bound when only one binding is possible: the
callee declares one binder of that resource family, and the caller owns
exactly one instance of it. Nothing is matched by name or by position, and
two candidates are never chosen between; the call is then refused with the
map entry to write. The bound instance still has to satisfy the callee's
requirement, arguments included.

<!-- verified-example: mdtests/a_hidden_record_resource_is_held_without_a_name.md -->
```click
int32 twice(struct pair* p) {
    owns pair(p);
    ensures result >= 0;
}
```

The transition is the one a named contract's proof arguments already take.
A `consumes` binder removes the caller's instance. An `owns` binder returns
the same identity with fresh post-call fields, related to its entry fields
only by the callee's guarantees, so a field the callee does not mention is
unknown afterwards. Caller instances the map does not mention frame unchanged.

An instance the callee `produces` does not exist before the call, so the
caller introduces it with `let`:

<!-- verified-example: mdtests/authority_named_import_cross_pool_transfer.md -->
```click
let { after: after } = step(move, { before: before });
```

The introduced name is an ordinary owned instance afterwards: it can be folded
into a parent as a child, or returned by the caller's own `produces` clause.

A call run by the implicit tail or a bare `step()` holds what it produces under no
name. At the function's exit, a `produces` binder held under no name takes
the one owned instance of its family that no name holds, by the same rule a
call binds a binder its map leaves out: the function declares one produced
binder of that family, and the exit holds exactly one such instance. An
instance the proof names, `let { left: l } = unfold(t)`, is never taken, so
a proof can still fold the binder itself after the return. Its
clause then checks the instance's arguments, so an instance at other
arguments is refused there
(`mdtests/produced_binder_refuses_another_arguments_instance.md`). An `owns`
binder whose own instance a call consumed takes such an instance the same
way (`mdtests/owned_binder_takes_the_call_result.md`). A client of a
consuming and producing callee needs no step map:

<!-- verified-example: mdtests/produced_binder_takes_the_call_result.md -->
```click
int32 set_and_get(struct cell* c, int32 x) {
    consumes before: cell_at(c);
    produces after: cell_at(c);
    ensures result == x;
    ensures after.value == x;
}
```

A non-mutex output may reuse the name of an instance consumed by the call.
Its current arguments and fields come from the produced contract; `old(...)`
still observes the caller's entry instance. Reuse does not let a call overwrite
another live instance. Multiple named outputs use a destructuring pattern:

<!-- verified-example: mdtests/c_call_binder_transport_multiple_produces.md -->
```click
let { first: a, second: b } = step(split_cells);
```

A produced binder that no output pattern introduces is an error.

#### Value parameters

A function contract can state a value its C signature does not carry by
declaring it `let name: type;`, with a scalar type and no initializer, as a
named contract declares its value parameters. Its clauses then use `name`:

<!-- verified-example: mdtests/cstr_at_value_parameter_names_a_length_the_c_signature_lacks.md -->
```click
extern uint64 string_length(const uint8* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}
```

The value is not a C argument and nothing is passed at run time. The
function's body is proved for every value of it
(`mdtests/cstr_at_value_parameter_is_proved_for_every_length.md`). An `owns`
clause returns the instance it received, so `old(n)` is the length at exit
(`mdtests/cstr_at_owned_value_parameter_keeps_its_length.md`). A value
parameter may not take the name of a C parameter or a C variable
(`mdtests/a_value_parameter_cannot_take_a_c_variable_name.md`). A clause
names the value; it does not name the instance, so `views s: cstr_at(p, n)`
and `owns s: R(p, _)` are refused with this form as the repair.

At a call each value parameter takes the argument of the one instance that
agrees with every other argument of the clause that mentions it, owned or
viewed by the caller. A call map gives the value instead, by the callee's
parameter name, without restating the call's arguments:

<!-- verified-example: mdtests/cstr_at_call_map_gives_the_length_of_a_string_a_call_assembles.md -->
```click
step(string_length, { n: n });
```

The map's value is evaluated at the call's state
(`mdtests/step_value_map_gives_a_let_parameter_its_value.md`,
`mdtests/step_value_map_takes_the_frontier_call.md`). It grants nothing: the
call still requires the clause at the value, so a value whose string the
caller neither holds nor can assemble is refused
(`mdtests/cstr_at_call_map_refuses_a_length_the_caller_holds_no_string_for.md`,
`mdtests/step_value_map_value_still_requires_its_clause.md`), and a value of
another type is refused
(`mdtests/step_value_map_value_has_the_parameter_type.md`). With no map
entry, no matching held instance, or two that differ at the parameter, the
call is refused with the parameter named and the entry to write
(`mdtests/cstr_at_value_parameter_needs_a_held_string.md`,
`mdtests/cstr_at_value_parameter_refuses_an_ambiguous_choice.md`); equal
values are not searched for.

A C library contract's value parameters are named the same way: the
library's `strlen` declares `let n: uint64;` and views `cstr_at(bytes, n)`,
so a sidecar writes `step(strlen, { n: 2u64 })`
(`mdtests/cstr_readable_witness_stated_before_call.md`).

The selected `modeled-pthread` runtime declares named mutex binders too.
Initialization takes `state` and produces `lifetime`; destruction takes
`lifetime`. For example, initialization can be written
`let { lifetime: life } = step(pthread_mutex_init, { state: initial });`
and destruction as
`step(pthread_mutex_destroy, { lifetime: life });`.
The input/output names belong to the runtime declaration; `life` and `initial`
are caller names. The former initialization key `invariant` is no longer
accepted. See the [checked lifecycle example](https://github.com/clicklang/click/blob/master/mdtests/mutex_lifetime_named_runtime.md).

A preserving helper may declare `owns lifetime: mutex_live(mu)` or
`owns guard: mutex_guard(mu)` and receive the named authority through an
ordinary call map. These names preserve the exact initialization or acquisition,
not just the pointer. They have no model fields or body to unfold.

A helper may also declare `owns access: mutex_use(mu)`. A call such as
`step(helper, { access: life });` can lend a named `mutex_live` authority or
reborrow a named `mutex_use` authority. The map selects that exact permission;
the helper receives a scoped use permission, and the caller recovers its original
authority and name when the helper returns. Nested helper calls follow the same
rule. Unary `mutex_use` permits balanced locking without granting protected
payload ownership. See the [checked nested example](https://github.com/clicklang/click/blob/master/mdtests/mutex_use_named_nested_call.md).

Named primitive children and theorem parameters, and general
consuming/producing primitive helper clauses remain unsupported. The complete
[mutex contract design](../../internals/mutex-resource-contracts.md) distinguishes
these supported forms from the planned protected-state and storage outputs.

Every call step has one output bundle. The `result` key names the C value;
other keys name the contract's produced resources. The pattern selects names
without changing the call or its resource effects:

<!-- verified-example: mdtests/call_result_in_condition.md -->
```click
let { result: r } = step(classify);
```

This is how a proof refers to a result the C never stores, as in
`if (f(x))` and `return f(x);`, where the branch fact and the callee's
guarantee are otherwise about a value with no name. The bound name is an
ordinary value in propositions and keeps denoting that returned value after
later statements; `result` on a `return f(x);` path is that same value. A
`let` on a call whose result the C discards is an error, and so is a name that
is already a C local or a proof-local binding. The map is still written, as
`{ }` when the callee declares no instance binder at all.

A call can bind both kinds of output together:

<!-- verified-example: mdtests/call_result_and_produced_resource.md -->
```click
let { result: status, output: checked } = step(set, { input: input });
```

`result` is reserved for the C value in a step output pattern. All produced
resources must be named; binding the C value is optional. The ambiguous
single-name form is rejected for both calls and assignment steps. Assignment
steps use `let { result: value } = step();`. The output bundle is a binding
interface, not a stored or copyable resource aggregate.

The callee's binder names come from its own sidecar, so that sidecar must be
declared before the proof that calls it. A named contract supports the same
input map and output pattern:

<!-- verified-example: mdtests/named_contract_call_output_bindings.md -->
```click
let { result: status, output: done } = step(Repair, { input: dirty });
```

This selects `Repair` for the current C call. Its C arguments come from that
call; its resource binder names come from the named contract. The verifier
requires established contract membership for the actual callee and its call
signature, checks the preconditions, and performs the contract's ownership
transition. The output pattern optionally names the C value and names every
produced resource. Direct and function-pointer calls use the same rule.

## Verifier primitives

Verifier primitives are part of the language, not the Click library. The
kernel or the C front end gives each one its meaning, so none can be
implemented or unfolded in Click. Every sidecar sees them without an import.
They are written in Click syntax in `library/primitives.click` and
`library/c/builtins.interface.click` only so that the parser declares them; the
[library reference](../library/index.md) does not list them. The documentation
gate checks each declaration below against that source.

The seven resources are declared as
[abstract resources](#read-and-write-resources), so none has a Click body
and none grants memory access by itself. The kernel rules described under
each entry govern how it is created, consumed, transferred, and counted.
Those rules cover mutex operations, atomic publication, population folds,
and heap allocation.

### Mutex acquisition authority

#### `mutex_guard`

**Declaration:** `abstract resource mutex_guard(mutex: void*);`

**Meaning:** Owns one current acquisition of a modeled mutex. The built-in
resource has exclusive unit ownership, no view, and no memory authority.
Use `owns mutex_guard(mu)` inside a declared-resource body. Folding consumes
the existing guard and unfolding returns it; proving `held(mu)` cannot create
it. Contracts may preserve a direct `owns mutex_guard(mu)` input or a folded
guard-bearing instance. Independently checked helpers can unfold and refold
wrappers, but cannot change mutex protocols. Direct clauses return the entry
acquisition. Named primitive binders and consumed/produced guards remain
unsupported.

**Verified use:** [`mdtests/mutex_guard_resource_body.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_guard_resource_body.md).

### Mutex lifecycle authority

#### `mutex_live`

**Declaration:** `abstract resource mutex_live(mutex: void*);`

**Meaning:** Owns the lifecycle authority for one initialization of a modeled
mutex. Initialization creates this exclusive unit resource. Locking currently
requires it to be available; destruction consumes it. A previous initialization's
owner cannot authorize operations after reinitialization at the same address.
It supplies neither an acquisition nor memory access, and cannot be viewed or
counted.

Use `owns mutex_live(mu)` directly in a preserving contract or inside an
exclusive declared-resource body. Folding consumes the owner; unfolding returns
it. Preserving helpers retain the entry initialization and cannot change mutex
protocols. Missing authority is reported as `Requires owns mutex_live(mu)`.

Initialization requires owned, aligned storage and reserves it against ordinary
writes until destruction. Synchronous helpers can borrow lifetime permission
through `mutex_use`. Worker transfer, named primitive binders, and lifecycle
`consumes`/`produces` contracts remain unsupported.

Automatic objects containing initialized mutexes cannot leave scope until
those mutexes are destroyed, even when their authority is folded away. This
covers normal and abrupt scope exits. Ambiguous symbolic mutex pointers are
refused conservatively rather than assumed separate from local storage.

**Verified use:** [`mdtests/mutex_live_wrapper.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_live_wrapper.md)
and [`mdtests/mutex_live_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_live_contract.md).

### Borrowed mutex lifetime

#### `mutex_use`

**Declaration:** `abstract resource mutex_use(mutex: void*);`

**Meaning:** An owned permission to use an initialized mutex while its caller
retains lifecycle responsibility. Use `owns mutex_use(mu);` in a preserving
helper contract. Calls borrow an available `mutex_live(mu)` owner or reborrow
an existing use permission; returning restores that exact source. A helper's
input grants neither lifecycle ownership nor protected-memory access.

The current implementation supports synchronous preserving helpers and nested
calls, including contracts with ordinary owned memory and stable views. It
retains the protocol freeze: initialization, destruction, acquisition, and
release inside these helpers remain unsupported. `views`, quantities, named
primitive binders, consumed/produced use permissions, and worker transfer are
also unsupported. Missing call-site authority is reported as
`Requires owns mutex_use(mu)`.

**Verified use:** [`mdtests/mutex_use_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_use_contract.md)
and [`mdtests/mutex_use_mixed.md`](https://github.com/clicklang/click/blob/master/mdtests/mutex_use_mixed.md).

### One-shot publication rights

#### `publisher`

**Declaration:** `abstract resource publisher(flag: void*);`

**Meaning:** The right to publish one payload through the C11 `atomic_int`
flag at `flag`, written `publisher(flag, P(args))` with the payload's resource
type. `atomic_init(flag, 0)` with `{ payload: P(args) }` creates it in the
modeled-pthread runtime. A release store of a nonzero value consumes it
together with a folded `P(args)`. It is unique per flag, grants no memory
access, and may be transferred to a worker. A second release store is reported
as requiring `owns publisher(flag, P)`.

**Verified use:** [`mdtests/publication_one_shot_handoff.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_one_shot_handoff.md)
and [`mdtests/publication_second_release_store_has_no_publisher.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_second_release_store_has_no_publisher.md).

#### `subscriber`

**Declaration:** `abstract resource subscriber(flag: void*);`

**Meaning:** The right to receive the payload published through the flag at
`flag`, written `subscriber(flag, P(args))`. An acquire load marks it as read
through the loaded value. The C branch that knows the value is zero keeps the
right, and the branch that knows it is nonzero receives an owned `P(args)` in
its place. It is unique per flag and grants no memory access by itself. Loads
without it receive nothing.

**Verified use:** [`mdtests/publication_one_shot_handoff.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_one_shot_handoff.md)
and [`mdtests/publication_unpublished_branch_does_not_receive.md`](https://github.com/clicklang/click/blob/master/mdtests/publication_unpublished_branch_does_not_receive.md).

### Population authority

#### `authority`

**Declaration:** `abstract resource authority();`

**Meaning:** `authority(reference(p))` is the exclusive control resource for
one population of the declared resource type `reference(p)`. The empty
population may be established with `fold(authority(reference(p)))` only in the
execution proof that created `p`'s storage. It may be retired with
`unfold(authority(reference(p)))` only when its member count is zero. Its
members may be field-free with private owned memory, observed by their current
`count(...)` and moved by direct authority/member helper contracts. An
ordinary field-free control can package counter memory, authorities, and facts
relating the memory to population counts. Ordinary helper contracts transfer
these controls, concrete members, and checked symbolic groups.

Local families can also have C or integer proof fields. For example,
`authority(ticket(p))` governs separately named `ticket(p)` instances; their
identities and field values remain distinct even when their arguments agree.
`let first = fold(ticket(p), { serial: 1 });` creates one member, and
`unfold(first)` consumes that exact member. Both operations require the matching
owned authority. `count(ticket(p))` observes the population total, not field
values or ownership of individual members. Retirement requires zero members.
A wildcard authority such as `authority(ticket(pool, _))` governs all exact
arguments of that local family. Both aggregate and exact counts include separate
occurrences with equal arguments. Private bodies remain exclusive even when
instances share their family arguments.

Preserving helpers take a named member through ordinary `owns` contracts and
retain its proof fields through explicit postconditions. They can unfold and
restore its private body while the caller keeps the authority control closed;
the same population occurrence stays reserved across the preserving call. A
member alone does not permit observing `count(...)`. Verified helpers can
create or consume named members when their checked input partition supplies the
governing authority. Creation needs an increment bound; consumption needs the
exact owned occurrence. Unary and wildcard imports preserve arbitrary entry
totals and record relative effects without anonymous member rights. Assumed
interfaces may preserve named ownership but cannot perform these lifecycle
effects. Symbolic quantities of heterogeneous named instances remain unsupported.

**Verified use:** [`mdtests/authority_named_field_members.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_named_field_members.md).

**Verified use:** [`mdtests/authority_named_field_private_helper.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_named_field_private_helper.md).

**Verified use:** [`authority_control_wrapper_tracks_memory_and_member_count_through_open_scopes`](https://github.com/clicklang/click/blob/master/src/surface/tests/authority_private_body_tests.rs).

A count and an equal C counter can have different checked term representations.
To transfer increment definedness, explicitly rewrite the count to the counter
using the control's equality and establish the nonnegative bound as needed.
For example, `rewrite(count(item(pool, _)), pool->checked_out)` can transport
`defined(pool->checked_out + 1)` inside an opened control. Nonnegativity alone
does not establish increment safety: the count can still be `2147483647`.

**Verified use:** [`authority_count_defined_through_control.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_count_defined_through_control.md)
and [`authority_count_defined_at_max_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/authority_count_defined_at_max_rejected.md).

### Allocation authority

#### `allocation`

**Declaration:** `abstract resource allocation(base: int32*, bytes: int32);`

**Meaning:** Owns the lifetime authority for the live heap block whose base
pointer is `base` and whose size is `bytes` bytes. A successful `malloc`,
`calloc` or `realloc` produces it beside ownership of the block's cells, and a
nonnull `free(p)` consumes it with complete ownership of the block, and is
refused when it is not held. The kernel names it
`ResourceFact::ALLOCATION_RESOURCE_NAME`: it is an exclusive token with no
body, it grants no read or write access by itself, and an owned positive
instance supplies the fact that `base[0..bytes]` lies inside one block. The base
argument accepts any modeled data, pointer-array or struct pointer; the owned
range keeps the pointer's own element width. An `extern` allocator contract
writes `produces allocation(result, bytes);`
([C allocation](c.md#heap-allocation)), or `allocates(result, bytes);` when
the allocation is new, a block no earlier pointer reaches
([fresh allocations](c.md#fresh-allocations)).

The declared byte count is an `int32`, and argument 1 also accepts a
`uint64` (`size_t`) count, as argument 0 accepts any data pointer. `malloc`,
`calloc` or `realloc` of a symbolic `size_t` size proved to fit `PTRDIFF_MAX`
makes a block with a 64-bit size, whose token holds a `uint64` byte count: a sidecar states it
as `allocation(p, n * 4u64)` or `allocation(p, bytes)`, and returns it, passes
it to a callee, or frees it like any other. A `uint64` count is admitted
under `malloc`'s no-wrap decision (`1 <= bytes <= PTRDIFF_MAX`, or
`1 <= n <= PTRDIFF_MAX / k` for `n * k`) wherever a token is formed, and a
count of the other format than the block's token does not name it; the
refusal names both formats ([C allocation](c.md#heap-allocation)). A signed
64-bit count is refused.

**Verified use:** [`mdtests/heap_malloc_struct_null_check_free.md`](https://github.com/clicklang/click/blob/master/mdtests/heap_malloc_struct_null_check_free.md),
[`mdtests/external_allocator_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/external_allocator_contract.md),
[`mdtests/a_bounded_size_t_element_count_allocates_a_64_bit_block.md`](https://github.com/clicklang/click/blob/master/mdtests/a_bounded_size_t_element_count_allocates_a_64_bit_block.md),
[`mdtests/an_extern_allocator_states_a_size_t_allocation_size.md`](https://github.com/clicklang/click/blob/master/mdtests/an_extern_allocator_states_a_size_t_allocation_size.md),
and [`mdtests/a_callee_frees_a_64_bit_block_it_consumes.md`](https://github.com/clicklang/click/blob/master/mdtests/a_callee_frees_a_64_bit_block_it_consumes.md).

### `__builtin_constant_p`

#### `__click_constant_p_unknown`

**Declaration:** `int32 __click_constant_p_unknown() { ensures result == 0 or result == 1; }`

**Meaning:** The value of the GNU builtin `__builtin_constant_p`, which the C
frontend lowers to a call of this function. Whether the compiler folds the
builtin's operand to a constant depends on optimization, so nothing is known
about the result beyond its being 0 or 1, and a proof covers both.

**Kind:** an `extern` contract, so its one guarantee is an explicit verification assumption, listed in [trust](../../concepts/trust.md).

**Verified use:** [`mdtests/c_builtin_constant_p.md`](https://github.com/clicklang/click/blob/master/mdtests/c_builtin_constant_p.md) checks that a claim must hold for both values.

## User-defined tactics

A `tactic` declaration names a reusable proof step with a contract. Its
clauses are a function contract's: `consumes`, `produces`, `owns`, `views`,
`requires`, and `ensures`. Its `by` block proves that contract once, at one
point of execution: it may unfold, fold, apply theorems and earlier tactics,
and prove facts, but it runs no C, so `step`, `step_until`, `loop`, `branch`,
and `outcomes` are refused in it. The block ends where its last step leaves the
proof: every produced instance must be held and every `ensures` an available
fact.

<!-- verified-example: mdtests/user_tactic_reshapes_owned_resources.md -->
```click
tactic divide(p: struct pr*) {
    consumes x: both(p);
    produces y: first(p);
    produces z: second(p);
    ensures y.tag == 7;
} by {
    unfold(x);
    let y = fold(first(p), { tag: 7 });
    let z = fold(second(p), { tag: 0 });
    have y.tag == 7;
}
```

A proof applies it like any tactic, by name, with the binder map a call step
uses:

<!-- verified-example: mdtests/user_tactic_reshapes_owned_resources.md -->
```click
let { y: y, z: z } = divide(p, { x: x });
```

An application first proves its argument evaluation obligations and the
instantiated `requires` clauses at the caller's frontier. It uses the same
`by` and `requires` proof suffixes as `step`, with implicit `close()` for
omitted proofs. Once the obligations are proved, the application consumes the
mapped inputs, binds produced instances to the names in the `let` pattern, and
adds the `ensures` facts. No C statement executes and memory stays the same.
`click expand` writes the call-site proofs alongside the application.

A tactic may apply itself. That is what makes it more than an abbreviation: a
recursive tactic covers a structure of symbolic size, such as converting a
linked list of any length one node at a time, which no fixed sequence of
`fold`s can. The recursive application is the induction hypothesis, so the
tactic must declare a `decreases` measure, written after the binders it reads
(`decreases links_len(x.model);`). Each recursive application of a numeric measure
owes the measure's descent as available facts: the measure at the
application is nonnegative and smaller than at the tactic's entry
(`mdtests/user_tactic_recursion_converts_a_list.md`). A recursion with no
measure is refused. A bare numeric parameter uses the same obligations.
A named structural binder (`decreases x;`) instead requires the passed
instance's model to be strictly contained in its entry model, through the
constructor arms established on the path
(`mdtests/user_tactic_recursion_uses_a_structural_measure.md`). Anonymous resource measures use the same retained finite-witness evidence
as ordinary calls.

Tactic parameters use Click's `name: type` syntax and are C scalars and
pointers in this release. The literal `0` supplies a typed null pointer at a
pointer parameter; other integers and integer variables do not implicitly
convert to pointers (`mdtests/user_tactic_accepts_null_pointer_arguments.md`).
A tactic may not take the name of a built-in tactic
or a C function, may not declare `diverges`, `throws`, or `constructs`, and
applies only itself and tactics declared before it, in the module that
declares it. An application runs at an execution frontier before the function
exits. See [User-defined tactics (design)](../../internals/user-defined-tactics.md)
for the kernel rule.

## Booleans

`Bool` is Click's logical sort, written capitalized like `Integer`. Its
values are `true` and `false`; it has no integer value and no order. A
`Bool` pure function's application, a `Bool` parameter of a pure function or
theorem, and a proposition used as a value are `Bool` values, and so is a C,
C++ or Rust `bool`: a function head keeps its language's type name (`bool` or
`_Bool` in C, `bool` in C++ and Rust), and each means `Bool`. In Click's own
code, `function`, `predicate` and `theorem` signatures, `let` annotations,
fields and type arguments, the type is written `Bool`; a lowercase `bool`
there is an error ("`bool` is not a Click type; write `Bool`"). A Rust
sidecar writes Rust's `bool` in those positions, as it writes `i32`.

<!-- verified-example: mdtests/a_bool_pure_function_states_a_claim.md -->
```click
function positive(x: int32) -> Bool { x > 0 }
function in_range(x: int32) -> Bool { x > 0 and x < 10 }
function outside(x: int32) -> Bool { not in_range(x) }
function choose(flag: Bool, x: int32) -> Bool {
    if flag { positive(x) } else { false }
}

theorem three_is_in_range() {
    ensures in_range(3) by {
        unfold(in_range(3));
        close();
    }
}
```

- **Literals.** `true` and `false` are literals wherever no C binding of that
  name is in scope. C's `true` and `false` are conveniences rather than
  reserved words, so a C parameter, local or global named `true` keeps its C
  meaning inside its function's contract
  (`mdtests/a_c_name_spelled_true_keeps_its_c_meaning.md`). A Click binder
  (a Click parameter, `let`, or quantifier variable) may not use either
  name (`mdtests/a_click_binder_spelled_true_is_refused.md`).
- **Typing.** `Bool` has equality and nothing else. Two `Bool` values are
  equal when they have the same truth. A `Bool` compared with an integer,
  ordered, or used in arithmetic, an implicit promotion included, is an
  error that suggests `b as int32` or a comparison with `true` or `false`:
  `flag == 1` for a C `bool` is refused, and is written `flag` or
  `flag as int32 == 1` (`mdtests/c_bool_parameter_range.md`). A `bool`
  literal compares only with a `Bool`; comparing an integer, pointer or
  other value with `true` or `false` is a type error.
- **`b as F`.** The cast of a `Bool` to an integer format `F` is 1 when `b`
  holds and 0 otherwise (rule C1 of `design/machine-integers.md`). So
  `b as int32 == 1` is `b`, `b as int32 == 0` is `not b`, and a cast known
  to be unequal to 0 is 1. A C function that returns its `bool` parameter as
  an `int` is specified `ensures result == flag as int32;`.
- **A `Bool` value as a claim.** A value written alone where a proposition
  is expected is the claim that it holds: `requires flag;`, `ensures result;`
  for a C function returning `bool`, and `ensures in_range(3);` for a call
  of a `Bool` pure function. `b == true` and `b != false` are the same
  claim, and `not b`, `b == false` and `b != true` are its negation, with no
  lemma between the forms
  (`mdtests/bool_negation_and_disequality_agree.md`). The value must be a
  `Bool`; an integer is not read with C's nonzero truth, so `requires count;`
  for an `int` is refused
  (`mdtests/an_integer_value_is_not_a_proposition.md`). A bare call of a
  pure function is read this way; a predicate call is unchanged.
- **`Bool` pure functions.** A `-> Bool` body is a `Bool` value: `true`,
  `false`, a `Bool` parameter or binding, a call of a `Bool` function, a
  comparison, `and`, `or`, `not` or `implies` of such values, or an `if`,
  `match` or `let` whose results all are. A proposition written as the value
  is its truth value: `x > 0` is `if x > 0 { true } else { false }`, which
  is `x > 0` itself, and a connective opens into conditionals that each test
  one comparison. Only this body, and the branches of its `if`, `match` and
  `let`, read a proposition as a value; everywhere else a comparison is a
  proposition, and C fragments keep C's `int` comparisons. A quantifier or
  predicate call is not a `Bool` value. An integer anywhere the body can
  produce a value is a type error
  (`mdtests/an_integer_body_for_a_bool_function_is_refused.md`).
- **Reasoning.** A `Bool` application is a term of the kernel's logical sort:
  `unfold(f(x))` files `f(x) == body`, `rewrite` with a `Bool` equality
  replaces one side by the other wherever a `Bool` is read, and a `Bool`
  conditional is opened only when its condition is decided. The range
  `b == true or b == false` is a disjunction, proved like any other with a
  case split such as `if b { ... } else { ... }`.
- **A C or C++ `bool` is a `Bool`.** A C or C++ `bool` parameter, local,
  call result or return value is a `Bool` value, so `b` claims that it holds
  and `not b` that it does not, as the test `if (b)` decides. A conversion
  of an integer to `bool` is the test `x != 0`, and promoting a `bool` to an
  integer gives `b as int32`. So `ensures early implies result == 7;` meets
  the branch the code took with no comparison with zero
  (`mdtests/a_c_bool_parameter_is_a_claim.md`). A `bool` object is one byte
  holding 1 or 0; see [C](c.md).
- **Rust.** A Rust sidecar writes the type `bool` as Rust does, and a
  parenthesized comparison there is a `Bool` value, `result == (x > 3)`
  ([Rust](../rust.md#signatures-in-rust-syntax)). In a C or C++ sidecar
  that operand is refused
  (`mdtests/a_parenthesized_comparison_is_a_value_only_in_rust.md`).

## Untyped pointers

`Pointer` is Click's untyped pointer, written capitalized like `Bool` and
`Integer`: an address and a provenance with no pointee type, like LLVM's
opaque `ptr`. A type belongs to the operation that uses a pointer, not to
the pointer. It is a type of Click's own positions (parameters, results,
binders, `let`, `load<T>`, casts); a function head writes its language's
type, and `Pointer *` is not a type.

<!-- verified-example: mdtests/untyped_pointer_load_of_a_pointer_field.md -->
```click
int32 *next_of(struct node *s) {
    views s->next;
    ensures load<Pointer>(&s->next) == s->next;
    ensures result == load<Pointer>(&s->next) as (int32 *);
}
```

- **Reads.** `load<Pointer>(a)` reads the pointer cell at `a`, whatever
  object pointer type the cell was declared with; its value is the pointer
  stored there.
- **Conversions.** Every object pointer converts to and from `Pointer`,
  implicitly at a parameter or binding and explicitly as `p as Pointer` or
  `q as (T *)`. The conversion keeps the value: it is not a C conversion, so
  a cast to a character pointer forms no byte view and `void *`'s rules do
  not apply. Function pointers are not `Pointer`s.
- **Equality.** `p == q` compares the whole value, address and provenance,
  also between a `Pointer` and a typed pointer.
- **No pointee.** `*q`, `q[i]`, `q + k` and `q - k` are refused ("a
  `Pointer` has no pointee type; cast it to a typed pointer or use
  `load<T>`"), and so is a `views` or `owns` range `q[a..b]`, which counts
  elements ("a `Pointer` has no pointee type to count a range in").
  `byte_offset(q, n)` is the `Pointer` `n` bytes on, and `load<T>(q)`
  reads a `T` there
  (`mdtests/untyped_pointer_byte_offset.md`,
  `mdtests/untyped_pointer_has_no_pointee.md`,
  `mdtests/untyped_pointer_range_is_refused.md`,
  `mdtests/untyped_pointer_owned_range_is_refused.md`).

## Propositions

Click proposition connectives are words:

<!-- verified-example: mdtests/proposition_connectives_quantifiers_and_old.md -->
```click
result == x and not (result != x)
result == x implies result >= 0
forall (k: int32) { 0 <= k and k < n implies p[k] == old(p[k]) }
exists (k: int32) { 0 <= k and k < n and p[k] == x }
```

Do not use C logical operators such as `&&`, `||`, or `!` in Click
propositions. Those remain C-fragment syntax.

The right side of `implies` and of `and` is read only where its left side
holds, as C's `&&` evaluates it, and the right side of `or` only where its left
side fails, so a right side's definedness is owed only there, as
`left implies requirement` for `implies` and `and`: `s >= 64u64 or (1u64 << s) == 2u64` owes
nothing for the shift, and lowers as written whatever the facts say.
A right side that is undefined wherever it is read, such as
`s < 64u64 or (1u64 << s) == 2u64`, is refused
(`mdtests/false_disjunction_requires_defined_right_requirement.md`). A
literally true left side, as in `64u64 >= 64u64 or (1u64 << 64u64) == 2u64`,
lowers to the left side alone
(`mdtests/true_disjunction_skips_undefined_right_requirement.md`).
`s < 64u64 and (1u64 << s) >= 1u64` owes nothing for the shift
(`mdtests/a_conjunction_reads_its_right_side_only_where_its_left_holds.md`),
and `s >= 64u64 and (1u64 << s) == 2u64` is refused
(`mdtests/a_true_left_conjunct_cannot_hide_an_undefined_right_side.md`). Such a
guarded requirement is established where its left side establishes it, so
`requires x > 0 implies y / x > 1` owes nothing
(`mdtests/an_implication_owes_its_consequents_domain_only_where_its_antecedent_holds.md`).

A comparison binds looser than every expression operator, which differs from C
for `&`, `^` and `|`. Parenthesize a comparison operand whose outermost
operator is one of those three: `(x & 1) == 0`, not `x & 1 == 0`, which is
refused. See
[Contract-expression precedence](grammar.md#contract-expression-precedence).

Range proposition helpers:

<!-- verified-example: mdtests/range_helpers_over_memory.md -->
```click
(lo..hi).all(|k| { p[k] <= x })
(0..3).any(|k| { p[k] == x })
```

`.all` lowers to a guarded bounded universal proposition. `.any` lowers to a
bounded existential proposition when its bounds are symbolic; concrete `.any`
ranges still unroll to a finite disjunction. While lowering the range body, the
elaborator assumes the item is inside the range, so bodies such as `p[k] == x`
can use `viewable(p[lo..hi])` for memory safety.

Prefer these range combinators for guarded memory reads. A plain proposition
such as `exists (k: int32) { lo <= k and k < hi and p[k] == x }` does not let
the earlier conjunct guard the later memory read during lowering.

Existential goals are proved explicitly in proof scripts with `witness`.
Values follow the outermost existential binders in declaration order, and
may supply one binder or several with `witness(value, ...)`. Pure theorem scripts also
support `int32` and pointer witnesses, alongside `Integer` and algebraic
witnesses. The value must have the binder's type, and the instantiated body
still needs a proof. A declaration-level `let` alias can be a witness value;
it retains the value from its declaration when a proof introduces a variable
with the same name. See [the pure witness example](https://github.com/clicklang/click/blob/master/mdtests/pure_machine_witness.md).
For a symbolic `.any`, the range item name is the existential binder:

<!-- verified-example: mdtests/range_helpers_over_memory.md -->
```click
ensures found: (lo..hi).any(|k| { p[k] == result }) by {
    step_until(function.exit);
    witness(lo);
    close();
}
```

## Special forms

`old`, `at`, `exact` and `defined` are the four special forms: built-in syntax
that looks like an application but changes how its argument is read or
lowered, so none of them can be written as a Click function. The first three
are point selectors, which pick the point that names a read and produce a
value; `defined` is a proposition about whether evaluating its argument is
defined.

| Form | Kind | Written where | Reference |
|---|---|---|---|
| `old(e)` | point selector | term | [`old(...)`](#old) |
| `at(point, e)` | point selector | term, proposition or resource | [`at(...)`](#at) |
| `exact(place)` | point selector | term | [`exact(...)`](#exact) |
| `defined(e)` | definedness | proposition | [requirements](#requirements) |

See [special forms](../glossary.md#special-forms) in the glossary for what
falls outside the set.

## `old(...)`

`old(expression)` is a [special form](#special-forms) that evaluates a
contract expression in the function-entry state. It is sugar for
`at(function.entry, expression)`. It is mainly used in postconditions and invariants:

<!-- verified-example: mdtests/proposition_connectives_quantifiers_and_old.md -->
```click
ensures p[0] == old(p[0]);
ensures forall (k: int32) { 0 <= k and k < n implies p[k] == old(p[k]) };
```

Inside `old(...)`, `result` is unavailable.

Contract expressions accept native scalar casts to `int8`, `uint8`, `int16`,
`uint16`, `int32`, `uint32`, `int64`,
`uint64`, `int128`, and `uint128`, including a cast on the left of a comparison.
A cast retains the native conversion semantics; it does not infer representable
ranges or identify a narrowed observation with its source. Wide casts let
sidecars name the explicit conversions in imported C++ expressions, such as
`n / d as int128`. Narrow casts use the existing conversion rules;
`defined(x as uint16)` still needs the modeled range guards. Checked narrow
boundaries and historical casts are in
[`contract_narrow_scalar_casts.md`](https://github.com/clicklang/click/blob/master/mdtests/contract_narrow_scalar_casts.md).
Wide examples are in
[`wide_contract_scalar_casts.md`](https://github.com/clicklang/click/blob/master/mdtests/wide_contract_scalar_casts.md).

Native scalar object pointers also support the checked byte-view cast
`p as (uint8 *)`, with an unqualified target that inherits the source qualification.
A claim such as `result == p as (uint8 *)` compares allocation identity
and byte offset, rather than numerical addresses. The cast preserves the
source pointer's const qualification and grants no ownership, read permission,
or initialization. Pointer arithmetic after the cast counts bytes;
`old(p as (uint8 *))` selects the entry-state pointer. Integer origins, pointer-to-pointer
origins, and reverse casts from bytes to wider object types are rejected. See
[`contract_byte_pointer_casts.md`](https://github.com/clicklang/click/blob/master/mdtests/contract_byte_pointer_casts.md).

Contract expressions accept integer casts such as `x as uint32` and `x as int8`,
including `old(p->value as uint32)`. A cast is C's conversion, as GCC and Clang
compute it: the value modulo 2^N of the destination type, defined for every
operand, so a 64-to-`uint32` cast keeps the low 32 bits
(`mdtests/a_narrow_specification_cast_is_always_defined.md`). The checked
conversion, which owes the destination range, is written `to_T(...)` over an
`Integer` (see [Mathematical integers](#mathematical-integers)). An argument
to a pure function's machine-integer parameter converts the same way C
converts a call argument
(`mdtests/a_pure_function_argument_converts_modulo_its_parameter_type.md`).
The operand must be a current scalar expression, including a pure-function
call; put `old(...)` or `at(...)` around the whole cast to read at another
point. Casts retain their selected point
even when the underlying field is subsequently updated.

A contract may also cast an opaque `void *` parameter of the function under
contract to a struct pointer and describe the object through the result:

<!-- verified-example: mdtests/fork_join_worker_direct_contract.md -->
```click
views (argument as (struct range_job *))->begin;
owns (argument as (struct range_job *))->output[
    (argument as (struct range_job *))->begin..(argument as (struct range_job *))->end];
ensures range_filled(argument as (struct range_job *));
```

The cast retypes the pointer for the clause; it does not change the pointer's
value or provenance, and the C body's own conversion reaches the same object.
The direct `argument as (struct T *)` form accepts a `void*` C parameter and
records one target struct per parameter for proof synthesis. Contracts may
also write `pointer as (void *) as (struct T *)` for a current object-pointer expression,
including a typed struct pointer, field, or resource parameter. A pointer to
a struct's initial member converted this way points to the struct (C11
6.7.2.1p15), so its bounds are the struct's. `pointer as (uint8 *) as (struct T
*)` converts from the byte view of the pointer's allocation, as C code that
steps back from a member with `container_of` does. This explicit
form retains the target layout on the expression and does not assign a layout
to the source parameter. Integer and function-pointer operands are rejected.
Source const qualifications survive the conversion; field reads and writes
still require their ordinary memory permissions. Put `old(...)` or `at(...)`
around the complete cast or field expression to read at another point.

<!-- verified-example: mdtests/contract_object_pointer_casts.md -->
<!-- verified-example: mdtests/contract_object_pointer_casts_rejects_missing_view.md -->
<!-- verified-example: mdtests/contract_object_pointer_casts_rejects_const_write.md -->
<!-- verified-example: mdtests/contract_object_pointer_casts_rejects_integer.md -->
<!-- verified-example: mdtests/contract_object_pointer_casts_rejects_function_pointer.md -->

When `old(p)` is passed as an array argument to a pure Click function or
predicate, it becomes an entry-state Click array ref. For example,
`permutation::permutation(p, old(p), 0, 2)` compares post-state `p` to entry-state `p`.
See [Surface Click and Kernel Click](../../concepts/surface-and-kernel.md).

## `program::` and qualified names

### File-qualified C objects

In a C sidecar, `verifying "dir/counter.c";` supplies the default alias
`counter`. The last filename component without its extension must be a
Click identifier and available as a qualifier. Use `as` to choose a
different alias or claim a name that would otherwise be inferred for
another file. An explicit alias takes effect after its declaration.

If two unaliased files share a stem, a reference through that stem is
ambiguous. Give at least one file a distinct explicit alias. Inferred
aliases leave Click library paths, datatype namespaces, `click::` and
`program::` available for their usual uses.

This example uses the default `left` and an explicit `right_file` alias.

<!-- verified-example: mdtests/qualified_static_resource.md -->
```click
verifying "left.c";
verifying "right.c" as right_file;

resource both() {
    owns left::count;
    owns right_file::count;
    fact right_file::count == 19u64;
}
```

`counter::count` refers to the file-scope C object declared in
`counter.c`, including a private `static` object. The alias identifies
the declaration. Ordinary calls still need their declared resources,
supplied initially by the program-entry proof or transferred by a
caller. One resource can own objects from several files.

Use the existing memory syntax: `&counter::count[0..1]` owns the storage of a
scalar, `cache::entries[0..16]` owns array elements, and
`counter::state.value` names a struct field resource. Owning a pointer variable
is different from owning the memory to which its value points. Resource facts
describe any contents that the resource's abstraction promises to clients.

Qualified objects also work in expressions, including `old(counter::count)`
and `counter::state.value`. Private objects with identical names in different
files remain distinct; qualifications of the same external object retain its
shared identity. This does not make private names visible in another C file.

A mutating wrapper can transfer its private field to a pointer-taking helper
and return ownership with the updated contents:

<!-- verified-example: mdtests/private_state_mutation_reset.md -->
```click
unsigned long left() {
    owns left_file::state.value;
    ensures left_file::state.value == integer::uint64_wrapping_add(old(left_file::state.value), 1u64);
    ensures result == left_file::state.value;
    ensures result == integer::uint64_wrapping_add(old(left_file::state.value), 1u64);
}
```

Here `left_file` aliases the C file containing `state`; its unchanged C wrapper
calls `bump(&state)`. Ownership is transferred, not recreated on each call.
The fixture covers repeated calls, reset, and another file's independent
`state`. The `unsigned long` increment wraps in C, so the contract states it
with `integer::uint64_wrapping_add` from `click::integer`; written with `+`, it
would compare exact Integers and claim the counter never wraps. An implicit
64-bit integer return conversion to `int` converts modulo
2^32, as GCC and Clang compile it, like the explicit `(int32)` cast.

For a function-local static, include the function name:

<!-- verified-example: mdtests/qualified_function_static_ownership.md -->
```click
owns counter_file::increment::calls;
```

This names the same storage as the unqualified `calls` inside `increment`.
Callers can transfer its ownership, and expressions such as
`old(counter_file::increment::calls)` refer to its value. Qualification grants
no access by itself and never initializes or replenishes the resource.
Ordinary automatic locals and parameters cannot be named this way. If several
block scopes in a function declare statics with the same name, the reference
is rejected as ambiguous.

This syntax supports file-scope and function-local static scalars, scalar
arrays (including multidimensional arrays), and struct objects. It does not
qualify functions as values or arrays of structs.
Explicit aliases must be unique and cannot share a name with a specification datatype.

### Program binding references

`program::name` explicitly refers to the binding named `name` in the verified
program, resolved as the program itself resolves it at that point: its
parameters and locals, then file statics and globals. The form is the same in
every source language. It is distinct from Click built-ins and contract
bindings with the same name. In particular, bare `result` is the function's
contract result, while `program::result` is a parameter or local named
`result`. The contract return
value has a separate internal binding, so a postcondition can use both names.
After function exit, a parameter reference denotes its logical input value.
Use `old(program::result)` or `at(function.entry, program::result)` to refer explicitly to
the parameter's entry value.

In a Rust proof, `bytes.len()` reads the length of the slice named by `bytes`
at the selected point. A Rust local can shadow a slice parameter.
`program::bytes.len()` explicitly selects the Rust binding, and
`old(program::bytes.len())` reads the original parameter length.

C locals exist only while they are in scope. After function exit, refer to a
local through a recorded point:

<!-- verified-example: mdtests/c_local_named_result_state.md -->
```click
result == at(region(2).entry, program::result)
```

The AST retains this distinction; `program::result` is not converted to an ordinary
string variable and cannot be reinterpreted as contract `result`. Expansion
uses this form when an explicit proof must name an overlapping C
binding.

The same holds for every Click value name: in a loop's clauses and phases bare
`iterations` is the loop's pass count, and `program::iterations` a program variable
named `iterations`; diagnostics print that variable as `program::iterations`
([`a_c_local_named_iterations_is_written_program_iterations.md`](https://github.com/clicklang/click/blob/master/mdtests/a_c_local_named_iterations_is_written_program_iterations.md)).
The earlier language-named forms `c(name)` and `rust(name)` are refused with
the replacement, and a source alias cannot be named `program`
([`a_language_named_program_binding_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/a_language_named_program_binding_is_refused.md),
[`design/charon-trial/program-bindings`](https://github.com/clicklang/click/blob/master/design/charon-trial/program-bindings/bindings.click)).

Returning a pointer does not extend an automatic object's lifetime. A returned
pointer must refer to storage that outlives the call, such as caller-provided,
static, or live heap storage; a postcondition that dereferences a returned
pointer to a callee local is rejected.

## `at(...)`

`at(point, expression)` is a [special form](#special-forms) that evaluates a
contract expression as it was when the proof path was at that point. In a
proposition position, `at(point, proposition)` evaluates the complete
proposition there. A proof path reaches each point at most once, so the point
fixes the meaning:

```text
at(function.entry, x)
at(loop_label.entry, x)
at(region(0).entry, x)
at(region(0).exit, x)
at(region(0).entry, p[0] == 7)
at(region(0).entry, viewable(p[0..n]))
```

Where a resource is expected, in `separate(...)`, `contains(...)`, `preserve(...)`
or a `Resource` theorem argument, `at(point, resource)` evaluates the resource
descriptor at that point. It accepts memory, named instances, resource parameters,
and resource constructors using the same grammar. Parentheses only group:
`at(point, resource)` and `(at(point, resource))` mean the same thing.

For a named instance, `at(point, name)` names the instance as it was held at
that point. It is how a proof names an instance a call has since consumed,
which the current state no longer holds.
A point where the path did not hold `name` is refused with "resource instance `name`
is not owned at this state"
(`mdtests/a_consumed_resource_instance_is_named_at_a_mark.md`,
`mdtests/a_resource_instance_is_not_named_at_a_mark_where_it_is_not_held.md`).

A field read such as `at(saved, c.model)` keeps the model held at the
selected point, including any constructor and its payloads. The proof can
match on that saved value after unfolding the instance
(`mdtests/a_saved_resource_model_keeps_its_constructor_payload.md`).

Every selector names a region: a stretch of the program with an `.entry` and
an `.exit`. `function` is the whole body and `loop(i)` is a loop. The regions
`step()` crosses one at a time are the *atomic* regions, and `region(N)` is the
`N`th of them, zero-based, in executable preorder. A C statement's calls are
each an atomic region of their own, before the one that uses their result:
`p->x = next(p);` is two atomic regions, the call and then the store, so the
state after `next` returns is the call region's `.exit`.

A region can also be written as a chain, each link a region inside the one
before it and counted from zero there:

| Region | Names |
|---|---|
| `statement(i)` | the `i`th block item of the function body as written, declarations included |
| `S.statement(j)` | the `j`th statement `S` controls or contains; an `if`'s arms share one count in source order |
| `loop(i).statement(j)` | the `j`th statement of loop `i`'s body |
| `S.region(j)` | the `j`th atomic region of `S`'s own, in executable order |
| `S.call(f, j)` | `S`'s `j`th call of `f`, in the order the calls run |
| `S.call(j)` | `S`'s `j`th call of any callee, a call through a function pointer included, in the order the calls run |
| `call(f, j)` | the function's `j`th call of `f`, counting all its calls of `f` in the order they run |
| `call(j)` | the function's `j`th call of any callee, in the order the calls run |
| `loop(i).test()` | the decision of loop `i`, after any condition preparation; pure conditions have the same test region |
| `S.assignment(x, j)` | `S`'s `j`th atomic region of its own that assigns local `x` |
| `S.read(j)` | `S`'s `j`th atomic region of its own with an explicit scalar memory load |
| `S.and(j)`, `S.or(j)`, `S.ternary(j)` | `S`'s `j`th `&&`, `\|\|` or ternary operator whose operands make steps, where it decides which run; `.result` is its value on the path |

A statement's `.entry` is before its first atomic region, its own or a
child's. Its `.exit` is after its `if` or loop region when it is one, after its
last atomic region otherwise, and after its last statement when it is a block.
A chained region reads the state `step()` recorded at the atomic region it
resolves to. One that names a statement, region or call the function does not
have is refused with what it does have
(`mdtests/a_statement_region_past_the_written_statements_is_refused.md`).

<!-- verified-example: mdtests/statement_regions_name_points_of_statements_as_written.md -->
```click
have at(statement(1).call(f, 1).entry, y) == x + 1 by close();
have at(statement(1).region(1).entry, y) == x + 1 by close();
```

There `y = f(f(y));` is `statement(1)`, and its outer call is both its second
call of `f` and its second atomic region.

`call(f, j)` and `call(j)` on their own count the function's calls rather
than one statement's, so `call(twice, 1)` is the second call of `twice`
wherever it is written (`mdtests/a_function_level_call_is_named_among_the_function_s_calls.md`,
`mdtests/a_function_level_call_past_the_function_s_calls_is_refused.md`).
A Rust proof writes `f` as its path, such as
`call(result_values::ok_if, 0).result`.

A Rust function's statements as written are named the same way.
`statement(i)` is the `i`th statement of the body's block, its tail expression
included. `S.statement(j)` counts the statements of every block inside `S` in
source order, so an `if`'s arms share one count, and so do a `match`'s arms; an
arm whose body is no block is one statement. A closure is a function of its
own. Each region is in the innermost statement whose source holds the MIR it
was lowered from, so `step_until(statement(1).call(0).entry)` stops at the second
statement's call (`charon_rust_statements_as_written_name_their_calls`).

`.region(j)`, `.call(f, j)`, `.test()`, `.assignment(x, j)`, `.read(j)`,
`.and(j)`, `.or(j)` and `.ternary(j)` end a chain
and count only `S`'s own atomic regions, not those of statements nested in
it: an `if`'s own region is its test
(`mdtests/a_chained_region_ends_in_an_assignment_or_read.md`,
`mdtests/a_chained_assignment_counts_only_the_statement_s_own_regions.md`).

A call's region also has a value: `R.result` is the result of the call `R`
names, such as `statement(0).call(make, 0).result`. It is the value the
call returned, retained at the region's exit even if the source discards it.
It still names that result after every local or cell that held it has lost it,
and a fact the call produced lowers from it exactly
(`mdtests/a_call_result_is_spelled_by_its_call.md`,
`mdtests/a_discarded_call_result_keeps_its_call_name.md`). A pointer result
indexes by its pointee, so `R.result[1]` for a `uint8 *` result is its
second byte (`mdtests/a_byte_call_result_indexes_by_its_byte_pointee.md`);
a `void *` result has none and is cast first. Allocation regions also
expose their nullable return through `.result`. In C++, the region that
reserves storage for a materialized object exposes its address through
`.result` before construction. Reading a field still requires initialized
storage. Void calls and other regions that do not produce a result are refused
(`mdtests/a_void_call_has_no_result_value.md`). Click writes a value only the frontend's
temporary for a call held this way
(`mdtests/an_unbound_call_result_is_reported_by_its_call.md`).

A call's region also names the callee's copy of each by-value aggregate
argument: `R.parameter(name)` is the object the call copied the argument into,
read at the memory just after the copy, which is what the callee's contract
reads. It is an object, read one field (or one element of an array field, by a
literal index) at a time, as `statement(3).call(first, 0).parameter(p).a`. The
step that runs the call has it while it proves the call's requirements at its
pre-state, so a `requires` entry of that step can state one, and it names the
same copy after the call. A name the callee does not take as a by-value
aggregate, and a region whose call has not been prepared, are refused
(`mdtests/a_call_parameter_names_only_a_by_value_struct_parameter.md`).

<!-- verified-example: mdtests/a_by_value_struct_argument_is_spelled_by_its_call_parameter.md -->
```click
step() {
    requires statement(3).call(first, 0).parameter(p).a <= 1000u32 by close();
}
have statement(3).call(first, 0).parameter(p).a == x;
```

A completed volatile read exposes its observed value as
`R.read_event(i).result`, where `i` counts volatile reads in execution order
within the atomic region `R`; volatile writes do not count. For example,
`statement(1).read_event(0).result` and
`statement(1).read_event(1).result` distinguish the two observations in
`x = volatile_value + volatile_value`. Select an atomic subregion first when a
source statement contains several regions. If the region has exactly one read
and no call result, `R.result` is also accepted. A call result takes precedence.
These names retain the typed observed value after locals are overwritten;
they do not perform another read or grant permission to access memory. Mentioning
a volatile object in a specification likewise does not create a C access event. The
current sequential volatile model may give several observations equal values.
An unexecuted event or an out-of-range index is refused. `read_event(i)` selects
a result, not an `.entry`/`.exit` point or a stepping target
(`mdtests/volatile_read_event_results.md`,
`mdtests/volatile_read_event_requires_execution.md`,
`mdtests/volatile_read_event_rejects_false_value.md`).

An allocation region also exposes `R.allocation`, the fresh heap identity
reserved for its successful outcome. For example, `statement(1).allocation`
keeps this identity distinct from the nullable `statement(1).result`. The
name is available after the allocation step and survives reassignment and
`free`. Pointer casts and `byte_offset(R.allocation, N)` can use that identity
to name a typed range in a `memory(...)` descriptor.
Naming it does not prove that allocation succeeded or grant access
to freed memory (`mdtests/an_allocation_result_keeps_its_name_after_reassignment.md`,
`mdtests/an_allocation_name_does_not_keep_freed_memory_readable.md`).

A recorded region exposes `R.footprint`, a resource descriptor for its effects:
writes, mutable call resources, and allocation lifetime changes. It grants no
ownership. `separate(R.footprint, B)` is the preservation premise consumed by
[`preserve(...)`](../tactics/index.md#preservation). Effects
are recorded during execution; this property does not reconstruct history.
The current simple separation rule handles one checked transition. Longer
transports use individual transition footprints and explicit equality composition;
not every branch/loop boundary currently has a complete recorded footprint.

Click writes points the same way. A diagnostic, a suggested premise or an
expansion names a recorded point by its statement: `.entry` or `.exit` when
the point is one, and the statement's `.call(f, j)` or `.region(j)` otherwise.
A call that belongs to no statement as written is written `call(f, j)` among
the function's calls. Click writes `region(N)` only for another atomic region
that belongs to no statement as written, such as a `break` or a Rust drop the
compiler added, or in a function whose frontend records none.
Nested statements and loop bodies are in
`mdtests/statement_regions_count_the_arms_of_an_if_together.md` and
`mdtests/statement_regions_reach_a_loop_body.md`.

An execution proof can give its current frontier state a local name and use
that bare name as a selector later:

<!-- verified-example: mdtests/proof_mark_before_write.md -->
```click
mark before_write;
step();
have p[0] == at(before_write, p[0]) + 1;
```

`mark` is a simple tactic and does not move execution. Its name is scoped to
the proof, cannot be rebound, and is not a `step_until` target. Bare
`at(before_write, ...)` therefore means a proof-local mark, while
`at(loop_label.entry, ...)` continues to mean the entry of a named source
region.

`at(function.entry, expression)` is equivalent to `old(expression)`. The
proposition form reads every state-relative part of the proposition at the
same point. This matters for propositions such as `viewable(...)`: both the
address expression and the memory in which it is viewable come from the
selected point.

The contract `result` exists only once the function returns, so `old(...)` and
`at(...)` at any point but `function.exit` cannot name it; both are
refused where they are written (`mdtests/old_of_result_is_refused.md`,
`mdtests/an_entry_point_cannot_name_result.md`). A proof mark can name it,
since a proof may place the mark after the return. A C binding named `result`
is still written `program::result` inside `at(...)` or `old(...)`.

`at(function.exit, ...)` reads the state the function returns in. It is
available where `result` is: in a postcondition and in a proof step after
execution has returned, where it is the current path's state. It is refused
before the return. Each returned path has its own `result`, so
`transport(at(function.exit, P), P) using { }` closes a `result` goal on a
path whose own state proves it, and expansion writes that step on each such
path (`mdtests/a_returned_path_transports_a_result_goal_from_function_exit.md`,
`mdtests/a_function_exit_point_before_the_return_is_refused.md`,
`mdtests/a_function_exit_transport_of_a_false_result_claim_is_refused.md`).

`at(...)` reads locals as well as memory at the selected point. Inside
`at(...)`, reassigned parameters and declared scalar, pointer, and array
locals resolve to their values at that point. Outside `at(...)`,
function parameter names retain their ordinary contract meaning.

A mark before the first execution step can name an incoming by-value
aggregate used in a resource clause. For example, after `mark inputs;`,
`at(inputs, dst.data)` and `at(inputs, dst.size)` name the pointer and
length in the entry separation fact. The first step binds the private
parameter object used by the body.

<!-- verified-example: mdtests/by_value_parameter_entry_range_separation.md -->

`at(loop_label.entry, expression)` is supported inside invariants for that
same labeled loop code region. It evaluates `expression` at the loop's entry
point, just before the loop region starts, and uses that value for invariant
entry and preservation checks. Inside an explicit `maintain` proof, the same
form continues to denote the value at that pre-loop point; the value at
the arbitrary loop-head iteration being checked is the ordinary unwrapped
expression.

The expression and proposition forms of `at(region(N).entry, ...)` and
`at(region(N).exit, ...)` are supported in explicit proof-script claims after deterministic execution records that statement point.
`step()`, `step_until(...)`, and the implicit tail all record every
deterministic statement boundary they cross. Executing an annotated loop uses
its verified abstract rule and records both `at(loop_label.entry, expression)`
and the unique post-loop state `at(loop_label.exit, expression)`. Branches still
require explicit arm proofs and a checked join before the path reaches a
unique exit point.

`step_until(region(N).entry)` starts at the current execution frontier, so it can
follow earlier `step` or joined `branch` steps. The
target must be forward and reachable on that selected path; it cannot be used
to rewind execution or enter an unselected branch.

## `exact(...)`

`exact(place)` is a [special form](#special-forms): the read of `place` named
by the state in scope itself, with no version walk (`design/exact-reads.md`).
An ordinary read `p[i]` names the cell's version point, the state the
assumption-free version walk selects for the cell: after a store to another
object it is still the read named by the earlier state ([a read names its
version point](../../internals/raise-lower-principle.md#a-read-names-its-version-point)).
`exact(p[i])` is the read of the same cell named by the current state. Both
denote the same value; they are different kernel terms for it, and the
assumption-free load equality relates them.

| Surface | Read |
|---|---|
| `p[i]` | at `p[i]`'s version point, seen from the current state |
| `exact(p[i])` | named by the current state |
| `at(point, exact(p[i]))` | named by `point`'s state |
| `old(exact(p[i]))` | named by the function's entry state |

`place` is any place expression whose ordinary read is legal there, such as
`p[i]`, `h->next` or `*q`
(`mdtests/an_exact_read_takes_a_field_or_a_dereference.md`). The read's type
comes from the place.
It reads an integer, `bool` or pointer cell; a pointer read's provenance and
bounds owner are the same exact read. `exact` applies to the outermost read
only: `exact(p[i]->next)` reads `->next` exactly through the ordinary read of
`p[i]`, and `exact(exact(p[i])->next)` reads both exactly.

<!-- verified-example: mdtests/an_exact_read_of_an_unchanged_cell_equals_its_ordinary_read.md -->
```click
have exact(p[0]) == p[0] by close();
have old(exact(p[0])) == old(p[0]) by close();
```

`exact` grants no access permission and adds no facts. A C read after it
still needs its own resource
(`mdtests/an_exact_read_grants_no_access.md`). An operand that is not a
memory read, such as a parameter's value, is refused: "`exact` takes a memory
read, such as `p[i]` or `h->next`"
(`mdtests/exact_refuses_an_operand_that_is_not_a_memory_read.md`). A declared
resource argument and a resource fact cannot contain `exact`. `exact` is a
built-in form, so no predicate or function can be named `exact`.

## Pure Click functions

Click functions are specification-level value definitions, not executable C
functions. Their parameters are Click-native binders and therefore use
`name: type`, unlike attached C function signatures.

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function inc(x: int32) -> int32 {
    x + 1
}

function eq_as_int(x: int32, y: int32) -> int32 {
    if x == y { 1 } else { 0 }
}

function count3(p: int32[], x: int32) -> int32 {
    let initial = 0;
    (0..3).fold(initial, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

Supported expression features include parameters, literals, `+`, `-`, `*`,
`/`, `%`, `<<`, `>>`, `int32` bitwise `&`, `|`, `^`, unary `~`, indexing,
`let name [: type] = value; body`, `if proposition { then } else { else }`,
range `.fold`, typed specification lambdas and their application, and calls
to other Click functions. Specification functions accept explicitly typed
function parameters, and transparent `Prop` results support logical adapters;
see [Function parameters](grammar.md#function-parameters-in-specification-functions).
A fold accepts a lambda value as its step. `.all` and `.any` accept
proposition-valued lambdas (`fn(Index) -> Prop`); see
[Range predicates](grammar.md#range-predicates). See
[Range folds](grammar.md#range-folds) for its signature and compatibility
shorthand.

A function returning `bool` states a truth value, and its body may be a
comparison or a connective of comparisons: `function positive(x: int32) ->
bool { x > 0 }`. A call of it written alone is a claim, `ensures
positive(3);`. See [Booleans](#booleans).

A range's endpoints are both `int32`, both `uint64`, or both `Integer`, and
its item has that type. A `uint64` range is what a function over a `size_t`
or `usize` index uses, `(0..end).fold(...)` with `end: uint64`; a nonnegative
literal at the other end is that number
(`mdtests/a_range_fold_over_uint64.md`).

Recursive pure functions must declare a well-founded measure. One supported
form is a natural-number measure:

<!-- verified-example: mdtests/pure_recursive_function.md -->
```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}
```

Every direct or mutual integer-recursive edge must pass a nonnegative measure
strictly smaller than the caller's. The measure is one named `int32`
parameter; the function's other parameters and its result may have any type,
so a function can build a list while it counts down
(`mdtests/an_integer_measure_recursion_builds_a_list.md`).

A recursive algebraic datatype parameter can also be the named measure. After
matching it, recursive calls may pass algebraic fields bound by that match;
nested matches on already-smaller fields, multiple recursive fields, and
mutually recursive datatype groups are checked the same way. Calls remain
symbolic. Explicit `unfold` exposes one defining equation and leaves the next
recursive application opaque, so verification never guesses a recursion
depth. This total value semantics is intentionally stricter than C recursion,
which a `diverges` marker may opt out of; a pure function has no such marker.

General properties of symbolic recursive calls use theorem-level
`let hypothesis = induct(parameter)`. Scalar induction is explicit and strong:
applying the local hypothesis checks a strictly smaller argument of the
measure's type and the theorem's substituted requirements. An `int32` measure
also requires nonnegativity; a `uint64` measure uses unsigned order over its
complete native range. For a recursive
algebraic parameter, follow the induction declaration with an exhaustive
`match` on that parameter. The hypothesis makes the same theorem available
at each immediate recursive field:

<!-- verified-example: mdtests/algebraic_structural_induction.md -->
```click
let ih = induct(xs);
match xs {
    TestList::Nil => {
        ... // base case
    }
    TestList::Cons(head, tail) => {
        apply(ih(tail));
        ... // inductive case
    }
}
```

Constructor arities and exhaustiveness are checked, arm bindings are lexical,
and multiple recursive fields each receive an induction-hypothesis instance.
Mutual induction across different datatype families is not generated.
`close()` does not invent induction, and a pure function's `decreases` clause
remains definition-totality evidence rather than a theorem about the result.

Function contracts may also use contract-level `let` bindings:

<!-- verified-example: mdtests/contract_let_bindings.md -->
```click
int32 bounded_increment(int32 x) {
    let max: int32 = 2147483647;
    let expected: int32 = x + 1;

    requires x < max;
    ensures result_value: result == expected;
}
```

Contract-level lets are immutable lexical abbreviations. They are visible to
later clauses in the same function block, including `requires`, `ensures`,
`owns`, `views`, and region proof blocks. A contract-level let cannot reuse a C
parameter name or an earlier contract-level let name. Explicit type annotations
are checked when the binding is evaluated, and a value that does arithmetic on
a machine value requires one
([Integer specification arithmetic](#integer-specification-arithmetic)).

Use `old(...)` in the binding when the abbreviation must capture an entry-state
value. For example, `let data = old(owner->data);` gives later postconditions a
stable backing pointer even if the current `owner` metadata changes.

Proposition clauses may also use witness lets:

<!-- verified-example: mdtests/contract_let_where.md -->
```click
let k: int32 where k == x;

ensures result_matches_witness: result == k by {
    step_until(function.exit);
    witness(x);
}
```

`let name: type where proposition; body` means `exists (type name) {
proposition and body }`. Contract-level `let ... where` applies that shape to
each later proposition clause. The type annotation is required. The current
implementation supports this in proposition clauses; it is intentionally
rejected in `viewable`, `owns`, and other memory-segment expressions until
Click has a contract-wide witness environment.

In pure Click function parameters, `int32 p[]` and `int32* p` are treated as
array-ref parameters. `uint8 p[]` and `uint8* p` are also array-ref parameters,
with one-byte indexing and `uint8` loads. Indexing `p[k]` loads at the version
point carried by that argument. This is why `count(p, ...)` can be called
with either current `p` or `old(p)`.

Click array refs carry their element type. Passing an `int32[]` ref to a pure
Click function or predicate parameter declared as `uint8[]` is rejected. A
`char`, `signed char` or `unsigned char` array passed for a `uint8[]`
parameter is read through its byte view `p as (uint8 *)`, so a string literal
of signed `char` reads as unsigned bytes, and a call is the same term wherever
it is written, including the recursive calls an `unfold` exposes
(`mdtests/a_byte_function_reads_a_string_literal_as_unsigned_bytes.md`,
`mdtests/a_recursive_byte_function_evaluates_a_string_literal.md`).
The same typed array-ref model is used by loop-invariant spec lowering, so a
pure helper over `uint8[]` can appear in an invariant or inside `old(...)`.

The Click library provides byte-slice helpers over `uint8[]`: `bytes::count`,
`bytes::equal`, `bytes::equal_range`, `bytes::all_equal`, `bytes::contains`, and
`bytes::all_not_equal`. It also provides C-string predicates:
`string::prefix`, `string::len`, `string::cstr`, and `string::bounded`, whose lengths and bounds
are `size_t` (`uint64`) values as C measures them. These are ordinary Click
functions and predicates, not built-in kernel concepts.

In pointer-valued C contexts, the integer constant `0` is the null pointer
constant. It may initialize or assign a pointer, be returned from a pointer
function, be passed to a pointer parameter, or be compared with a pointer.
Pointer-typed datatype constructor fields use the same rule in function
contracts and pure expressions: a field declared `int32*` accepts `0` as its
typed null pointer. Nonzero integers do not implicitly convert to pointers.

Supported C accepts the struct shapes listed in
[struct subset](c.md#struct-subset). The C side lowers chained `obj->child->field` loads and stores at
LP64-aligned byte offsets while retaining intermediate struct-pointer types.
Click contracts can use field places in resources:
`views obj->field` and `owns obj->field`. The access resource also makes the
field viewable for symbolic execution.

Use `*obj` for the complete storage of a struct object:

<!-- verified-example: mdtests/owned_symbolic_separation_certificate.md -->
```click
owns *owner;
owns data[0..length];
...
have separate(memory(*owner), memory(data[0..length])) by close();
```

`*owner` is layout-aware: it denotes the imported C struct's aligned
size without exposing byte offsets or pretending that a pointer field is a
pair of source-level `int32` fields. Use `owner->field` for one field and
`*owner` for the complete object. When a proof exposes the object's
cells, wide integer fields take their own type while pointer fields are
held as pointer-width words that read back as pointers; the field's source
text is unaffected. Explicit ranges such as
`p[0..count]` remain the usual syntax for array storage.

`owns *p` and `views *p` cover every field of the object, including the
padding after each field, an embedded struct's fields and an inline array
field, so they replace a clause per field (`owns p->len; owns p->cap; owns
p->data;`) in a contract, a loop header and a resource body. Memory the object
points at is not part of it: a pointer field's pointee is still its own clause,
`owns *owner; owns owner->data[0..owner->cap];`. A function holding `*p` lends a
callee any of its fields and keeps the rest unchanged across the call
(`mdtests/whole_struct_lends_nested_and_array_fields.md`). Two differences
from the per-field list remain. A required `*p` carries the generated
`aligned(p, alignof(struct))` requirement described under
[Requirements](#requirements); a field clause does not. And the object is
held as `int32` cells, so a struct whose size is not a multiple of four bytes
has no `*p` form and is refused by name
(`mdtests/whole_struct_needs_a_whole_number_of_int32_cells.md`); own its
fields one by one. A struct with a flexible array member is outside the
supported C subset. A call can assemble `owns *p` from adjacent owned fields,
including byte fields, when their combined footprint covers every byte of
the object and the required alignment is established. A scalar field clause
covers its ABI slot up to the next field or the end of the struct, including
tail padding after the final field. Viewed fields cannot complete an owned
footprint; explicit byte fragments must cover padding too. See the
[byte-field regression](https://github.com/clicklang/click/blob/master/mdtests/whole_struct_reassembles_from_byte_fields.md)
and [tail-padding regression](https://github.com/clicklang/click/blob/master/mdtests/whole_struct_reassembles_from_padded_byte_field.md).
A file-scope struct named in `owns g` or `views g` covers that complete
object, with the same size and declared field types as `*p` when `p == &g`.
The same rule applies to a qualified name such as `unit::g`; a pointer-valued
global named alone still denotes its pointer slot.

Surface Click also has documented low-level memory reads for addresses that do
not have a recoverable C source place:

- `load<T>(pointer)` reads the object at `pointer` as `T`, a scalar, data
  pointer, or function pointer ([Typed loads](grammar.md#typed-loads))
- `byte_offset(pointer, bytes)`

Typed loads select memory from the surrounding clause independently of the
point the pointer value was read at. `load<int32>(old(p))` reads current memory through
the entry-state pointer, while `old(load<int32>(p))` reads entry-state memory.
A read in a specification, through `load<T>` or a C place such as `*p`, needs
no read permission and no initialized storage: it denotes the value that memory
holds and grants nothing. Reading the same memory in C code needs both.

`address(pointer)` is the `uint64` integer representation of an object pointer
under the LP64 profile. It is the spec form of the C cast
`(unsigned long) pointer` and denotes the same kernel term: the address keeps
the exact source pointer. `address(p) == address(q)` holds when `p == q`
does, but not conversely: it is what a C comparison between pointers states,
and it carries no permission from one pointer to the other. A contract
`p == q` also compares the subobjects that pointers formed by C member
access designate: a call cannot satisfy `requires q == p` with the arguments
`&pair->first + 1` and `&pair->second`, though their addresses are equal.
A scalar member address written in a contract, `&p->f`, designates the
member as the C expression does.
`address(p) == 0` is decided as `p == 0`, and a comparison with an integer
that has no pointer origin stays undecided. Rewriting the pointer to null reduces
its address to `uint64` zero, also inside arithmetic with symbolic operands.
Contracts use it to describe words that hold a pointer in integer form,
such as `ensures node->word == address(next)`
or, for a tagged word, `requires node->word == address(next) + 1`. Tag
operations on such words (`+`, `|`, `& ~m`, `& m`) and the cast back to a
pointer are checked rewrites whose obligations come from `aligned`; the
memory model describes the rules. The tag set with `|` may be a constant or
a masked read `x & m`, as in rbtree's `rb_color(rb) | (unsigned long)p`,
whose bound is the mask; two words whose tags are so bounded compare unequal
when their pointers are distinct and both aligned past the bound. A mask
must clear the whole tag: `& ~1` on a word tagged with 3 is refuted rather
than producing a word that still carries bit 1.

Explicit `close() using { aligned(p, 8); }` can also certify reading low
tag bits: `((address(p) + word) & 7) == (word & 7)`, including unsigned
wraparound. The read mask must be contiguous low bits, and the selected
alignment must cover those bits. This also applies to a bounded tag packed
with `|`, such as `(((word & 7) | address(p)) & 3) == (word & 3)`.

The low-level reads and `byte_offset` are Surface Click escape hatches, not
Kernel Click syntax. The canonical
renderer prefers `owner->field` whenever imported layout origin identifies
the address. Expansion may emit a low-level read only when no source field
place is available.

Symbolic folds remain `RangeFold` value terms in the kernel and can be
reasoned about by supported fold laws. Pure `int32` folds over one or two
items can also retain their fold terms. With literal bounds, callbacks that
return the accumulator, the item, or an `int32` literal can retain their
fold terms at any range length. For a nonempty range, checking uses the
seed, final item, or literal, respectively. Other concrete callbacks can
be evaluated by unrolling.


### Methods

A value of a Click type is read with its type's methods, `receiver.method(args)`,
in every sidecar language. The parser records the call as written, and
declaration expansion resolves it by the receiver's type once that type is
known, so a `match` arm's binder, a `let` binder, a theorem binder and a pure
function's result read alike. A slice, `Slice<T>` from
`click::rust::slice`, has `len()`, `as_ptr()`, an index `s[i]` (a read
through its data), and the subslices `s[a..b]`, `s[a..]` and `s[..b]`, which
owe `a <= b <= s.len()` where they are evaluated
([Rust slices](../rust.md)). A method the receiver's type lacks is refused
with the type and the method, "`Slice<uint8>` has no method `size`". Any
other library type's methods are its library module's functions over it:
the function named after the method whose first parameter is that type, so
a `Vec<uint32>` reads `v.len()` as `vec::len(v)`, and its index `v[i]` is
`vec::get(v, i)` (`mdtests/a_vec_value_reads_with_its_library_methods.md`).
A program's own pure functions are not methods. A C or C++ value keeps its
own meaning: `s.f` on a struct and a member access on a class are resolved
from their declarations as before.

<!-- verified-example: mdtests/a_click_typed_value_reads_with_its_types_methods.md -->
```click
import click::rust::slice;

theorem slice_methods(s: Slice<uint8>) {
    requires 2u64 <= s.len();
    ensures s.len() == slice::len(s) by {
        close();
    }
    ensures s.as_ptr() == slice::as_ptr(s) by {
        close();
    }
    ensures s[1..].len() == s.len() - 1u64 by {
        close();
    }
}
```

## Predicates

Predicates return Click propositions:

<!-- verified-example: mdtests/sort3_sorted.md -->
```click
predicate sorted_range(p: int32[], lo: int32, hi: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}
```

Predicate calls are opaque by default. Requirements and loop invariants can
reuse predicate facts with exact non-pointer arguments and pointer arguments
matched through checked equality closure at compatible types. State arguments
remain exact. Click does not unfold predicate bodies unless a proof asks for it:

<!-- verified-example: mdtests/sorted_predicate.md -->
```click
ensures still_sorted: sorted(p, n) by {
    unfold(sorted(p, n));
}
```

Loop invariants are declared by the `loop` tactic when execution reaches that
loop. Predicate bodies needed by the loop rule can be exposed in its
`initialize` and `maintain` proofs:

<!-- verified-example: mdtests/loop_sorted_range_invariant.md -->
```click
loop carry_sorted {
    decreases 3 - i;
    invariant i >= 0 and i <= 3;
    invariant sorted(old(p), 3);

    initialize by {
        unfold(sorted(old(p), 3));
        unfold(sorted_range(p, 0, 3));
        ...
    }
    maintain by {
        unfold(sorted(old(p), 3));
        unfold(sorted_range(p, 0, 3));
    }
}
```

Either phase may be omitted, in which case Click supplies bounded automation
for that phase. `click expand` at the `loop` keyword materializes all omitted
phase proofs together.

Like pure Click functions, predicate array parameters are Click array refs.
A predicate can compare two arrays from different memory states when its caller
passes arguments such as `p` and `old(p)`.

## Write footprints

A function's externally visible write footprint is exactly the memory its
contract owns. There is no separate effect clause: `owns` permits stores and
reads, `views` permits reads, and a store outside the owned memory fails at
the store.

For an ordinary call whose checked owned inputs bound all its writes, `step`
can use separation between that resource bound and the live-view footprint.
This also works when the input is a folded recursive resource and the call
cannot name every byte it might write
(`mdtests/recursive_call_keeps_a_separated_live_view.md`).

Contract segment expressions are evaluated at function entry, so a shifted
segment such as `owns (owner->data + owner->len)[0..2]` continues to denote the
old two-cell tail after `owner->len` changes. Footprint matching uses proven
pointer equalities, including unchanged field loads across a finite chain of
certified memory effects.

A narrow write inside a composite the function owns is written as ownership
of the whole plus a promise about the cells it leaves alone; an owned piece
inside a viewed composite is not a footprint, because the composite's facts
may depend on that piece:

<!-- verified-example: mdtests/field_derived_precise_effect_after_metadata_write.md -->
```click
owns owned_buffer(owner);
ensures owner->data[0] == old(owner->data[0]);
```

Callers then frame the viewed remainder with no clause and no tactic, so a
contract does not restate `ensures owner->head == old(owner->head);` for a
cell it only views (`examples/ring-buffer`). A cell the contract owns,
consumes or produces is in its footprint, and its value after the call is
what the contract's `ensures` say: a frame for an owned cell the body leaves
alone, such as `ensures owner->cap == old(owner->cap);` beside a produced
resource, is still written, because callers rely on the contract and not on
the body. A
function that owns no memory must not write memory that was live at entry;
this is checked when the function contract is certified, so callers preserve
memory across a read-only callee with nothing to declare. Stack locals and
initialization writes to a function-fresh allocation are internal and never
part of the footprint. Ownership never waives allocation lifetime obligations.

File-scope and static storage is not caller memory, so a contract that declares
resources may store into such storage only inside the cells it owns: a `views`
clause, or ownership of a neighboring cell, does not authorize the store.
Resource slices of global and static arrays use the array's declared element
width, so `owns bytes[0..1]` on a `uint8` array covers one byte.

A loop may declare resources of its own beside its invariants, in the same
`owns` and `views` forms a contract uses:

<!-- verified-example: mdtests/loop_owns_preserves_symbolic_index.md -->
```click
loop {
    owns p[0..n];
    invariant i >= 0;
    invariant i <= n;
}
```

An unconditional plain-memory clause evaluates its pointer and bounds at loop
entry, before modified locals are havocked. For example, `views p[0..n]`
continues to describe the original physical range when the body advances `p`
and decrements `n`. An invariant such as `viewable(p[0..n])` separately owes
the current cursor and remaining range at each head. Named resource binders
retain their own argument and model rebinding rules.

A declared resource must be one the enclosing function already holds; a loop
cannot own what its function does not. The loop then has the shape of a callee:
its body executes owning exactly what the loop declared, with everything else
the function owns viewed rather than owned, so a body store outside the loop's
owned memory is rejected at the store. The loop's write footprint is the memory
it owns, so the function's other owned memory keeps its pre-loop value with no
invariant naming it. A loop that declares only `views` owns nothing and so
writes nothing. With no declaration, a loop inherits everything the function
owns, which is the default footprint an omitted clause already means.

Loop frames are described in [proof-workflow.md](../../concepts/proof-workflow.md)
and [memory-model.md](../../concepts/memory-model.md).

### Target byte order

`little_endian()` states that the selected execution target stores the least
significant byte first. It takes no arguments and is reserved as a built-in
proposition. C proofs receive this fact from a little-endian execution
environment; a big-endian environment supplies its negation. Pure theorems
have no target assumption and must require the fact explicitly. It is the
target premise of `integer::uint32_from_le_bytes`.


## Program termination proofs

After function bodies have been proved, program closing has an ordinary goal
combining the selected return promises, divergence policies, and callback safety.
An optional top-level `termination by { ... }` block supplies its proof. With no
block, or with proofs omitted at its end, the implicit solver runs on that goal.
Ordinary `have`, logical tactics, and `close()` work inside the block.

The propositions are `termination_returns("f")`, `termination_divergence("f")`,
and `termination_callbacks()`. Checked steps also expose `termination_local("f")`,
`termination_strict("f")`, and `termination_body("f")`. Quoted names identify
functions rather than proof variables. Negations record refused classifications;
these scoped propositions cannot be declared as assumptions in unrelated
contracts or theorems.

`click expand --claim program.termination file.click` writes a replayable block
of [termination checks](../tactics/index.md#termination-checks) and ordinary proof
steps. `click verify --trace-proof program.termination file.click` traces that
proof. Completion publishes the captured return promises after the ordinary
root goal closes and discovers no additional obligations.
