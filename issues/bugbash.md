# Bug bash: open soundness holes and C mis-models

Thirteen independent root causes. Every one has a reproduction that verifies
today while stating something the C does not guarantee: a false postcondition,
a definite answer where C leaves the behaviour undefined or unspecified, or a
program C rejects that Click accepts. All are against C11/C17 on the LP64
profile Click documents.

Five are critical: an ordinary contract over ordinary C is certified while
false, with no unusual tactics. The other eight are high: the trigger is
narrower, an unusual construct or an out-of-range value, but the accepted
claim is just as wrong. Nothing here is speculative; anything that could not
be made to reproduce has been removed rather than left as a lead.

This is deliberately a bundle rather than one file per problem, so the set
stays together while it is triaged. **Split it up as work starts**: when a
root cause is picked up, move its section into its own `issues/<name>.md`, add
the Open-list line, and delete the section here. Delete this file when the
last section is gone.

Sections are grouped by severity, not by fix order. Several say what *not* to
do: those directions were built and measured, and each broke sound proofs
elsewhere or lost a capability the tree uses. Read them before starting.

## Reproducing

Each regression is a self-contained pair. Write the files into an empty
directory and run:

```sh
click verify --time-limit 30s t.click
```

Exit 0 is the bug. Every pair below was re-run against the release binary and
reproduces. Each regression is intended to land as an mdtest whose `expect`
block is a rejection, so the diagnostic in the acceptance criteria is a shape,
not an exact string; where the fix makes a previously-rejected program verify
instead, land the positive test too.

---

## 1. Globals and statics assumed at their initializer on every entry

**Severity: critical.** Any function that reads a mutable global is certified
against its initial value, so a false postcondition about a global verifies
and composes into false claims about callers.

**Violated invariant.** A function may assume nothing about the value of an
object with static storage duration at entry beyond its declared contract. C11
6.2.4p3: such an object is initialized once before program startup and then
holds its last stored value.

**Mechanism.** `initialize_c_function_globals`
(`src/kernel/functions.rs:3005-3060`) stores `global.initial_value()` into the
slot whenever the entry state has no block for it, and every standalone
certification starts from a state with no global blocks. Function-local
statics take the same path a few lines below (`static_local.initial_value()`,
around `:3216`).

**Regression** (`mdtests/global_entry_initializer_rejected.md`):

```c
int32 counter = 3;

int32 increment_counter() {
    counter = counter + 1;
    return counter;
}

int32 read_counter() {
    return counter;
}

int32 run() {
    int32 ignored;
    ignored = increment_counter();
    return read_counter();
}
```

```click
verifying "t.c";

int32 increment_counter() {
    requires counter < 1000;
    mutable &counter[0..1];
    ensures result == old(counter) + 1;
    ensures counter == old(counter) + 1;
}

int32 read_counter() {
    ensures result == 3;
}

int32 run() {
    mutable &counter[0..1];
    ensures result == 3;
}
```

`run()` returns 4 in every execution; all three claims verify today. The
static-storage variant is the same bug:

```c
int32 counter() {
    static int32 calls = 0;
    calls = calls + 1;
    return calls;
}

int32 twice() {
    int32 a = counter();
    int32 b = counter();
    return b;
}
```

```click
verifying "t.c";

int32 counter() {
    mutable &calls[0..1];
    ensures result == 1;
}

int32 twice() {
    ensures result == 1;
}
```

`twice()` returns 2.

**Acceptance criteria.**
- Both sidecars are rejected; `read_counter`'s `ensures result == 3` fails for
  want of a precondition relating `counter` to 3.
- A sidecar that states the same claim under an explicit `requires counter == 3`
  still verifies.
- The existing global and static mdtests (`file_scope_globals.md`,
  `static_local_arrays.md`, `aggregate_static_effect.md`, and the rest of the
  file-scope family) still pass, or their contracts are updated in the same
  change with the added preconditions spelled out.
- Decide and document where initializer values may still be assumed. A
  designated program entry point is the natural place; nothing else is.

---

## 2. A callee contract with no effect clause is applied with zero memory havoc

**Severity: critical.** An omitted `immutable`/`mutable` clause is treated as
"writes nothing" instead of "writes anything", so a caller keeps stale values
for everything the callee actually wrote.

**Violated invariant.** Applying a verified function rule must not assume any
memory is preserved that the callee's certified effect claim does not cover. A
contract with no effect clause certifies no effect claim
(`contract_effect_claim_required` is false), so it licenses no preservation.

**Mechanism.** Verified-rule application (`src/kernel/functions.rs:991-1063`)
builds `mutable_ranges` from `function.contract_mutable()`; when that list is
empty it takes the `entry_state.memory.clone()` branch and emits no
`CMemoryEffectSummary` at all. An absent clause and a certified `immutable`
clause therefore reach the caller identically.

**Regression** (`mdtests/call_without_effect_clause_rejected.md`):

```c
int32 g = 0;

int32 bump() {
    g = g + 1;
    return 0;
}

int32 wrapper() {
    bump();
    return 0;
}

int32 caller() {
    bump();
    return g;
}
```

```click
verifying "t.c";

int32 bump() {
    requires g < 100;
    ensures result == 0;
}

int32 wrapper() {
    requires g < 100;
    immutable;
    ensures result == 0;
}

int32 caller() {
    requires g < 100;
    ensures result == old(g);
}
```

`wrapper` certifies `immutable` although it increments a global through
`bump`, and `caller` certifies that `g` is unchanged across the call.

**Acceptance criteria.**
- `wrapper`'s `immutable` claim and `caller`'s `ensures` are both rejected.
- Adding `mutable &g[0..1];` to `bump` makes `wrapper`'s `immutable` fail with
  the ordinary footprint diagnostic, and lets `caller` state a true claim.
- Document whatever is chosen in the contract reference next to
  `immutable`/`mutable`, since it changes what an omitted clause means.

**Do not use unbounded havoc at the call.** Adding a
"contract declares an effect clause" bit to `CFunction` and havocing all
non-stack cells when a call has neither a declared clause nor a
resource-derived frame rejects the regression below but breaks 15
mdtests that are not unsound, among them `const_global_table.md`,
`execute_modular_swap_get.md`, and `c_named_function_contract_pipeline.md`.
Those callees hold only `views` requirements and write nothing; a read-only
resource requirement is not an effect clause, so the call-site test cannot
tell them from a callee that writes a global.

The fix therefore belongs at certification, not at the call: check every
function's writes against its declared footprint, treating an omitted clause
as the empty footprint the callers already assume. `read_table` then certifies
unchanged because it writes nothing, while `bump` fails at its own write with
a diagnostic pointing at the store rather than at a caller that mysteriously
lost its facts. The obstacle is that the effect check currently runs only for
a claim the surface emits per written clause
(`src/surface/verification.rs:76`, `:1359`), and a resource-derived frame
deliberately carries no Effect claim
(`with_resource_derived_mutable_frame`), so the implicit case needs its own
path rather than a synthesized surface clause.

---

## 3. Globals assigned inside a loop are not havoced at the loop head

**Severity: critical.** The pre-loop value of a global survives the abstract
iteration, so a loop that increments a global is certified to leave it alone.

**Violated invariant.** The abstract loop head must forget every object the
body can modify. A by-name assignment to an object with static storage
duration is such a modification.

**Mechanism.** `havoc_loop_modified_locals` (`src/kernel/loops.rs:2340`)
refreshes only bindings that match `CLocalBinding::Object`; a global binding
falls through the `let ... else { continue }`. The memory havoc that would
otherwise cover the cell is gated on `statement_may_write_memory`
(`src/kernel/loops.rs:2441`), which does not count a by-name global assignment
as a memory write.

**Regression** (`mdtests/loop_global_not_havoced_rejected.md`):

```c
int32 g = 0;

int32 bump(int32 n) {
    int32 i = 0;
    g = 0;
    while (i < n) {
        g = g + 1;
        i = i + 1;
    }
    return g;
}
```

```click
verifying "t.c";

int32 bump(int32 n) {
    requires n >= 0 and n <= 100;
    mutable &g[0..1];
    ensures result == 0;
} by {
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    frame();
    simp();
}
```

`bump(5)` returns 5. The same hole applies to a function-local `static`.

**Acceptance criteria.**
- The sidecar is rejected; the invariant is too weak to conclude anything
  about `g` at the exit.
- Adding `invariant g == i;` lets the true postcondition `result == n` verify.
- Fix both halves: include global and static bindings in the modified-name
  havoc, and count by-name assignment to a static-storage object as a memory
  write for the havoc gate. A regression for each half.

---

## 4. Memory cells carry no width; retyping casts are accepted

**Severity: critical.** Eight findings share this root cause. Overlapping
accesses of different widths never invalidate each other, so a store leaves
readable stale values behind, and the frame checker measures a store by the
wrong number of bytes.

**Violated invariant.** A store must invalidate every cell whose byte range it
overlaps, and effect checking must measure a store by the width of the value
stored. Separately: the C0 reference says pointer casts other than
`void *` identity conversions are unsupported, and unsupported constructs are
rejected rather than approximated.

**Mechanism.** Cells in `src/kernel/primitives/memory_state.rs` are keyed by
`(block, offset)` with no width, so a 1-byte store at offset 1 does not touch
the 4-byte cell at offset 0, and a 4-byte store does not touch the byte cells
it covers. `src/surface/checking/effects.rs` compares a changed cell against
the declared range using the range's element width or the store's start
pointer. Upstream of both, `(uint8*)&x` and `(int64*)(void*)p` lower as
retyping in `src/languages/c/syntax.rs` instead of being rejected.

**Regression A**, stale word after a byte store
(`mdtests/byte_store_leaves_word_stale_rejected.md`):

```c
int32 byte_store_alias() {
    int32 x = 16909060;
    uint8* b = (uint8*)&x;
    b[1] = 0;
    return x;
}
```

```click
verifying "t.c";

int32 byte_store_alias() {
    ensures result == 16909060;
}
```

`x` is `0x01020304`; `b[1] = 0` clears one of its bytes, so the function
returns `0x01020004` = 16908804 on any little-endian LP64 target.

**Regression B**, a wide store escaping a narrow footprint
(`mdtests/wide_store_escapes_footprint_rejected.md`):

```c
int32 wide_store(uint8* b) {
    int32* w;
    w = (int32*) b;
    w[1] = 7;
    return 0;
}

uint8 caller(uint8* b) {
    int32 ignored;
    ignored = wide_store(b);
    return b[7];
}
```

```click
verifying "t.c";

int32 wide_store(uint8* b) {
    owns b[0..8];
    mutable b[0..5];
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

uint8 caller(uint8* b) {
    owns b[0..8];
    mutable b[0..5];
    ensures result == old(b[7]);
} by {
    execute();
    frame();
    simp();
}
```

`w[1] = 7` writes bytes 4 through 7, so `mutable b[0..5]` is false and `b[7]`
changes; both claims verify today.

**Acceptance criteria.**
- Decide the boundary first. If retyping casts stay unsupported, both
  regressions must fail at the cast with a source-positioned diagnostic, and
  that is a complete fix for the reachable cases.
- If retyping is to be supported instead, cells must become width-aware: a
  store invalidates every overlapping cell, and effect checking uses the
  stored width. Then both regressions fail on the memory or footprint check,
  and a positive mdtest shows a byte view of an `int32` reading the stored
  bytes correctly.
- Related findings to close with this one: an 8-byte store into an
  `int32`-indexed range needing only one owned element; a narrower store
  leaving the wider cell stale; the frame check measuring changed cells by the
  range's element width.

---

---

## 6. `at(L.entry, ...)` denotes two different states in one loop proof

**Severity: critical.** Inside a `preserve` proof the spelling means the fresh
havocked loop-head visit; after the loop it means the real pre-loop state. An
invariant proved under the first reading is exported under the second.

**Violated invariant.** One spelling, one program point. A fact proved about
the arbitrary head visit is not a fact about loop entry.

**Mechanism.** `src/kernel/api.rs:318-321` builds each
`CLoopPreservationContext` with `state: top_state.clone()` **and**
`loop_entry_state: top_state.clone()`, so the preservation context's notion of
loop entry is the havocked head. The surface driver records that state as the
loop `Entry` snapshot
(`src/surface/proof/execution_planning/loop_planning.rs:360-367`, `1273-1282`).
The documented behaviour in the `at(...)` section of the language reference
describes the head-visit reading, so the documentation is complicit and needs
to change with the code.

**Regression** (`mdtests/loop_entry_snapshot_rejected.md`):

```c
int32 c(int32 n) {
    int32 x;
    x = 0;
    while (x < n) {
        x = x + 1;
    }
    return x;
}
```

```click
verifying "t.c";

int32 c(int32 n) {
    requires n >= 5 and n < 1000;
    ensures result <= 1;
} by {
    step();
    step();
    loop as L {
        invariant x >= 0 and x <= n;
        invariant x - 1 <= at(L.entry, x);
    }
    step();
    have at(L.entry, x) == 0 by { simp(); }
    have result - 1 <= at(L.entry, x) by { simp(); }
    have result - 1 <= 0 by { rewrite(at(L.entry, x) == 0); assumption(); }
    have result <= 1 by { arithmetic() using { result - 1 <= 0; } }
    simp();
}
```

The second invariant is not inductive: `x` reaches `n >= 5` while
`at(L.entry, x)` is 0. The function returns `n`, yet `result <= 1` verifies.

**Acceptance criteria.**
- The invariant `x - 1 <= at(L.entry, x)` fails its preservation obligation.
- `at(L.entry, ...)` denotes the pre-loop state everywhere, including inside
  `preserve`. If the arbitrary head visit needs a spelling, give it a distinct
  one and document both.
- Update the `at(...)` section of `docs/reference/language/index.md` in the
  same change, and keep a positive mdtest where an invariant legitimately
  relates the current state to loop entry.

---

## 7. Literal and operator typing: `sizeof`, negated literals, `?:`

**Severity: high.** Thirteen findings share this cause. Each makes a mixed
signed/unsigned expression evaluate differently from C.

**Violated invariant.** The C0 frontend implements C's integer constant typing
(C11 6.4.4.1p5), `sizeof`'s type (`size_t`, i.e. `uint64` under LP64), and the
usual arithmetic conversions (6.3.1.8), or rejects the construct.

**Mechanism.**
- `src/languages/c/syntax.rs:11891-11921`: the unary-minus fast path folds
  `-<digits>` into an `Int32Literal` whenever the magnitude fits `2^31`, so
  `-2147483648` is `int32` INT_MIN where C has `long`. The positive literal
  path (`parse_integer_literal_expression`, `:13001-13048`) is correct, which
  is why `-(2147483648)` behaves and `-2147483648` does not.
- `sizeof` lowers to an `int32` literal, so `sizeof(int32) - 5` is signed where
  C computes it in `size_t` and wraps.
- The conditional operator keeps the selected arm's type instead of the common
  type of both arms.

**Regression A** (`mdtests/c_negated_literal_typing_rejected.md`):

```c
int32 t() {
    return -2147483648 < 0u;
}
```

```click
verifying "t.c";

int32 t() {
    ensures result == 0;
}
```

In C the literal is `long`, `0u` converts to `long`, and the comparison is
true: the function returns 1.

**Regression B** (`mdtests/sizeof_typed_int32_rejected.md`):

```c
int32 sizeof_cmp() {
    return sizeof(int32) - 5 < 0;
}
```

```click
verifying "t.c";

int32 sizeof_cmp() {
    ensures result == 1;
}
```

`sizeof(int32) - 5` is `size_t` arithmetic: `4 - 5` wraps to a huge unsigned
value, so the comparison is false and the function returns 0.

**Regression C** (`mdtests/conditional_operator_type_rejected.md`):

```c
int32 cond_type_cmp() {
    return (1 ? -1 : 1u) < 0;
}
```

```click
verifying "t.c";

int32 cond_type_cmp() {
    ensures result == 1;
}
```

The conditional's type is `unsigned int`, so `-1` converts to `UINT_MAX` and
the comparison is false: the function returns 0.

**Acceptance criteria.**
- All three regressions are rejected and the true claims verify.
- Implement the constant typing table by magnitude and base (decimal versus
  hex/octal differ in whether unsigned types are considered), type `sizeof` as
  `uint64`, and apply the usual arithmetic conversions to conditional arms.
- Where a combination is out of the modeled slice, reject it with a
  source-positioned diagnostic rather than approximating.
- Related findings closed by this one: negated hex literals losing
  unsignedness; unsigned wraparound in global constant initializers being
  reported as overflow; `-2147483648 / -1` reported as undefined behaviour when
  in C it is well-defined `long` division.

---


## 9. A store through `&local` in an inline header helper is dropped

**Severity: high.** The caller keeps the old value of a local the inlined body
wrote through a pointer.

**Violated invariant.** An inline helper executes on the caller's memory; a
store through a pointer to a caller local is visible to later reads of that
local by name.

**Mechanism.** Inline bodies from headers are checked at the call site on the
caller's memory (`src/languages/c/source.rs` expansion plus ordinary
execution), but the store does not go through the address-escape path that
syncs an address-taken local's named binding.

**Regression** (`mdtests/inline_helper_store_dropped_rejected.md`), a header
plus a source:

```c
/* include/hset.h */
#ifndef HSET_H
#define HSET_H
static inline int32 set0(int32* p) {
    p[0] = 9;
    return 0;
}
#endif
```

```c
/* t.c */
#include "include/hset.h"

int32 run_set0_local() {
    int32 n;
    int32 ignored;
    n = 100;
    ignored = set0(&n);
    return n;
}
```

```click
verifying "t.c";

int32 run_set0_local() {
    ensures result == 100;
}
```

The function returns 9.

**Acceptance criteria.**
- The sidecar is rejected and `ensures result == 9` verifies instead.
- The same test with the helper written as an ordinary function in the same
  translation unit continues to behave (it already does), so the regression
  pins the inline path specifically.

---

## 10. A reloaded pointer to a local is treated as a distinct block

**Severity: high.** After a call, a pointer loaded back out of caller-visible
memory no longer aliases the local it points to, and the resulting state is
contradictory.

**Violated invariant.** A pointer value loaded from memory that may hold the
address of a local must be able to alias that local. A state in which
`q == &x` holds and a store through `q` does not affect `x` is unsound
regardless of what is then proved from it.

**Mechanism.** The reload after a `CallHavoc` edge produces a symbolic pointer
in a fresh block rather than one that may alias existing blocks
(`src/kernel/functions.rs` call application together with the transport rules
in `src/kernel/memory_provenance.rs`).

**Regression** (`mdtests/reloaded_local_pointer_rejected.md`):

```c
void keep(int32** pp) {
}

int32 reloaded_store_hits_local(int32** pp) {
    int32 x = 1;
    int32* q;
    *pp = &x;
    keep(pp);
    q = *pp;
    if (q == &x) {
        *q = 2;
    }
    return x;
}
```

```click
verifying "t.c";

void keep(int32** pp) {
    requires loadable(pp[0..1]);
    consumes pp[0..1];
    mutable pp[0..1];
    ensures pp[0] == old(pp[0]);
    produces pp[0..1];
}

int32 reloaded_store_hits_local(int32** pp) {
    requires loadable(pp[0..1]);
    consumes pp[0..1];
    mutable pp[0..1];
    ensures result == 1;
    produces pp[0..1];
}
```

The branch is taken and `*q = 2` writes `x`, so the function returns 2. That
`ensures result == 7` also verifies is the tell: the post-call state is
inconsistent.

**Acceptance criteria.**
- The sidecar is rejected, and the state after the call proves no numeric value
  for `result` other than through the real aliasing.
- Add an inconsistency probe to the regression: a claim like `result == 7`,
  which no execution satisfies, must never verify.

---

## 13. Range byte counts wrap modulo 2^32

**Severity: high.** A huge or negative element range lowers to a tiny byte
footprint, so a `loadable` fact is certified for memory that was never claimed.

**Violated invariant.** The byte footprint of an element range is
`(end - start) * element_width` without wrapping.

**Mechanism.** Two sites multiply an element count by an element width with
the ordinary 32-bit term constructor and no overflow obligation:
`CMemoryRange::byte_footprint` (`src/kernel/primitives/contracts.rs:1197`),
which runs only when two ranges have different element widths, and
`loadable_base_and_bytes` (`src/surface/lowering/resource_lowering.rs:1357`),
which builds the `CMemoryLoadable` byte count. The latter is the path this
regression takes. It already rejects a constant reversed range, but the count
here is the symbolic `n`, so the wrap happens later, when the kernel folds
`n * 4` against the path's `n == 1073741825`.

Measured signature, with `loadable(p[0..1])` required: `n = 2^30` (byte count
folds to 0) and `n = 2^30 + 1` (folds to 4) both certify, while `n = 2^30 + 2`
(folds to 8) is correctly rejected. `n = -1` also certifies, which is
defensible: an empty range is vacuously loadable.

A fix needs a decision rather than a local patch: either carry byte extents in
64 bits, or emit a no-overflow obligation where an element range becomes a
byte count. The
memory model documents a 32-bit block extent, so the second is the smaller
change but needs an obligation channel at both sites.

**Regression** (`mdtests/range_byte_count_wraps_rejected.md`):

```c
int32 symn(int32 p[], int32 n) {
    return 0;
}
```

```click
verifying "t.c";

int32 symn(int32 p[], int32 n) {
    requires loadable(p[0..1]);
    requires n == 1073741825;
    ensures loadable(p[0..n]);
}
```

`(n - 0) * 4` wraps to 4, so a one-element loadability fact certifies a
4-gigabyte range. The mirror case is `views p[0..n]` with
`n == -1073741823`, which authorizes reading `p[0]` from an empty view.

**Acceptance criteria.**
- Both the wrapping and the negative case are rejected.
- Compute footprints in 64-bit, or emit a no-overflow obligation on range
  lowering; either way empty and reversed ranges stay empty.
- Audit the other range operations for the same gap: element-to-byte
  arithmetic without a side condition appears wherever a range is measured.

---

## 14. Intra-object array overflow is modeled as a flat access

**Severity: high.** The flat-access model is documented, which is why the
fix has to change the documentation with it; it still certifies a value for a
program whose behaviour C leaves undefined.

**Violated invariant.** An array subscript outside its own dimension is
undefined behaviour (C11 6.5.6p8) even when the containing allocation has more
bytes. Bounds are currently enforced only at allocation-block granularity.

**Mechanism.** Row-major flattening (`flatten_array_indices`,
`src/languages/c/syntax.rs:12888`) and inline array fields lower an inner index
into a flat offset, and only the block bound is checked. The flat-access rule
is documented in `docs/reference/language/c0.md`, so the documentation changes
with the fix.

**Regression A** (`mdtests/flat_array_inner_overflow_rejected.md`):

```c
int32 c() {
    int32 m[2][3];
    m[1][2] = 1;
    m[0][5] = 9;
    return m[1][2];
}
```

```click
verifying "t.c";

int32 c() {
    ensures result == 9;
}
```

**Regression B**, the more practical shape — an overflow of an inline array
field into the next field (`mdtests/inline_array_field_overflow_rejected.md`):

```c
struct rec {
    int32 buf[2];
    int32 next;
};

int32 spill(struct rec* r) {
    r->buf[2] = 7;
    return r->next;
}
```

```click
verifying "t.c";

int32 spill(struct rec* r) {
    owns object(r);
    ensures result == 7;
}
```

A genuine buffer overflow into the neighbouring field is certified as defined
behaviour with a predictable result.

**Acceptance criteria.**
- Both regressions are rejected with an out-of-bounds diagnostic naming the
  subobject.
- Emit per-subobject bounds obligations for inner dimensions and inline array
  fields; the containing block bound is not sufficient.
- Update the flat-access wording in `docs/reference/language/c0.md`, and keep
  the existing multidimensional and inline-array positive tests passing.

---

## 15. A `for` initializer's variable stays readable after the loop

**Severity: high.** C0 accepts a program C rejects, and proves a value for the
out-of-scope read.

**Violated invariant.** A variable declared in a `for` initializer is scoped to
the loop (C11 6.8.5p5). Naming it afterwards is a use of an undeclared
identifier, which is a constraint violation, not a value.

**Mechanism.** Not localized. `for` is lowered as sugar over `while` in
`src/languages/c/syntax.rs`; the initializer's declaration is emitted into the
enclosing block, so the binding outlives the loop it belongs to.

**Regression** (`mdtests/for_initializer_scope_rejected.md`):

```c
int32 for_initializer_scope_rejected() {
    int32 total = 0;
    for (int32 i = 0; i < 3; i++) {
        total = total + i;
    }
    return i;
}
```

```click
verifying "t.c";

int32 for_initializer_scope_rejected() {
    ensures result == 3;
}
```

**Acceptance criteria.**
- The C source is rejected with a source-positioned diagnostic naming `i`.
- A `for` loop whose index is declared before the loop, and read after it,
  still verifies.

---

## 16. Identical string literals are proved distinct

**Severity: high.** Whether identical literals share storage is unspecified,
so neither answer may be proved.

**Violated invariant.** C11 6.4.5p7: it is unspecified whether identical string
literals are distinct objects. A conforming implementation may merge them, so
a proof that two identical literals differ is a proof of something no
implementation is required to make true.

**Mechanism.** Each literal is installed under its own block identity, keyed by
the literal's generated name (`CMemory::string_literal_pointer` in
`initialize_c_function_globals`, `src/kernel/functions.rs:3006-3040`).
Distinct blocks compare unequal, so the comparison decides.

**Regression** (`mdtests/identical_string_literals_undecided.md`):

```c
int32 identical_string_literals_undecided() {
    uint8* first = "ok";
    uint8* second = "ok";
    if (first == second) {
        return 1;
    }
    return 0;
}
```

```click
verifying "t.c";

int32 identical_string_literals_undecided() {
    ensures result == 0;
}
```

**Acceptance criteria.**
- Neither `result == 0` nor `result == 1` is provable; the comparison stays
  undecided, and a proof needs both paths.
- A literal compared against itself through one pointer still decides equal.

---

## 17. A postcondition may read the storage of a returned local

**Severity: high.** A contract states a value in storage whose lifetime ended
when the function returned, and the caller may rely on it.

**Violated invariant.** An automatic object's lifetime ends when its block is
left (C11 6.2.4p6); a pointer to it becomes indeterminate, so a postcondition
may not read through it.

**Mechanism.** Not localized. The returned pointer keeps its `local:` block,
and the postcondition is lowered against the exit state where that block's
cells are still present.

**Regression** (`mdtests/returned_local_postcondition_rejected.md`):

```c
int32* returned_local_postcondition_rejected() {
    int32 value = 5;
    return &value;
}
```

```click
verifying "t.c";

int32* returned_local_postcondition_rejected() {
    ensures result[0] == 5;
}
```

**Acceptance criteria.**
- The postcondition is rejected: the frame's storage is gone at the exit
  state, so the load has nothing to read.
- A postcondition over storage that outlives the call, a heap allocation the
  function returns or a caller object it was given, still verifies.

---

## Tooling failures

These block use rather than admitting false claims, but the first one means the
CLI and the fixture gate disagree about the same input, which is its own
problem.

**T1. `click verify` rejects every source that calls `realloc`.** Extracting
the checked-in `mdtests/realloc_preserves_calloc_prefix.md` (expect: pass) into
a directory and running `click verify t.click` gives
`click: no C source defines realloc` and exit 1. The CLI's callee closure
(`src/surface/verification.rs:1440-1458`, `c0_statement_calls`) treats the
`realloc` builtin as an ordinary callee, while `malloc`, `calloc`, and `free`
are dedicated statement forms; the harness entry point does not compute that
closure. Documented `realloc` support is unreachable from the CLI. Acceptance:
that mdtest's sources verify through `click verify`, and a CLI test pins it.

**T2. `--changed-since` cannot resolve project-local headers.** A project with
`cap.h`, `m.c` containing `#include "cap.h"`, and a sidecar verifies with
`click verify`, but `--changed-since HEAD` (and `--explain`) fails with
`cannot resolve local include cap.h as cap.h in the source bundle`, with no
change in the tree. Incremental mode builds its source bundle without headers.
Acceptance: incremental verification of a project with local headers works, and
a header edit selects the functions whose translation units include it.

**T3. A trivial theorem produces a smart proof with no certificate.**
`theorem small(x: int32) { requires x < 10; ensures x < 20; }` under the default
prover fails with `smart proof for small.ensures_0 succeeded but did not
produce a pure surface certificate`. `ensures x <= 10` works. This is the
"smart success without a certificate" class that `CLAUDE.md` says blocks
feature work. Acceptance: the theorem verifies, or the search declines promptly
with an actionable diagnostic.

**T4. `execute()` emits a certificate the checker rejects** for `break` inside
an `if` inside a nested `while`. Same class as T3.

**T5. Panic (`unreachable!`) when a local struct initializer zero-fills a
`float`/`double` field.** A crash, not a wrong answer. Acceptance: the
initializer is either supported or rejected with a source-positioned
diagnostic.

---

## Checked and found sound

Recorded so the next pass does not re-cover this ground. Each was probed
directly against the release binary with claims that are false under C; each
was correctly rejected, and the corresponding true claims verified.

- Integer operators: signed division truncation and remainder sign, arithmetic
  right shift, `1 << 31` flagged, `INT_MIN / -1` flagged, precedence of `-`,
  `%`, `<<`, and `&` against `==`, chained comparisons, octal literals,
  `~0 == -1`, `(-1) & 255 == 255`.
- Signed/unsigned comparison `-1 < 1u` is false; `int32 + uint32` wraps
  unsigned; concrete `int32 + int64` computes in 64 bits.
- Control flow: `switch` fallthrough and `break` inside a `switch` inside a
  loop, `do ... while` running once, `continue` in `for` running the step,
  short-circuit evaluation with a division by zero on the right, the unselected
  arm of a conditional.
- Undefined behaviour at constant indices: local and global array
  out-of-bounds, uninitialized scalar, pointer, struct-copy and loop-body
  reads, missing return in a non-void function, pointer index scaling overflow.
- Frames: writing a global through a pointer under `immutable`, storing a fresh
  allocation's address into a global under `immutable`, a callee mutating a
  global with the caller claiming it unchanged, and a callback parameter
  shadowing a file-scope function.
- Resources: two `owns` clauses over aliasing arguments are rejected as
  overlapping; `views` and `owns` over the same cell are not assumed separate.
- Floating point with symbolic operands: NaN keeps the third path in
  `a < b` / `b <= a`, `a == a` is not assumed, `a != a` is not assumed false.
- Undefined behaviour inside `requires` is checked as a callee precondition at
  call sites, and an overflowing callee `ensures` instantiation yields no fact.
- Incremental selection re-verifies correctly after a callee contract change, a
  callee body change, a strengthened callee precondition, a caller body change,
  a global initializer change, an extern contract change, a theorem change,
  and a named-contract or algebraic type change.
- Sidecar/C signature mismatches (arity, parameter order, parameter type) and
  missing functions are rejected.
- The proof object and simple tactics: the reviewer assigned to
  `assumption`/`extract`/`rewrite`/`instantiate`/`enumerate`/`contradiction`,
  branch joins and splits, and the fact store produced no reproducible finding.
- The `prove_int32_*` axioms in `src/kernel/api.rs` were checked at their
  boundary values and are sound as stated.

## Ruled out

Reported during the review and refuted on inspection. Do not re-file.

- **An `extern` contract can state a false axiom.** True, and documented:
  `docs/reference/language/c0.md` says an `extern` declaration is applied as an
  explicit assumption. The trusted boundary is the feature.
- **Struct-pointer resource ranges use 4-byte logical units.** An internal
  spelling question, not a claim about C; the reproduction's postcondition is
  true.
- **`choose` witness ids collide with loop-invariant binder ids.** The reported
  route does not exist; the reproduction exits 1, and the "certificate failed
  round-trip validation" message it produces is a rejection, not an acceptance.
- **`click verify` exits 0 on a sidecar with no proof units.** Documented
  behaviour: a sidecar target verifies every claim in that sidecar, and there
  are none.
