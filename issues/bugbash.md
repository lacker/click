# Bug bash: soundness holes and C mis-models found on 2026-09-06

This file bundles the results of one adversarial review of the verifier at
`d6502258`. It is deliberately one file rather than one file per problem, so
the whole result set stays together while it is triaged. **Split it up as work
starts**: when a root cause is picked up, move its section into its own
`issues/<name>.md`, add the Open-list line, and delete the section here. Delete
this file when the last section is gone.

Every numbered section is an independent root cause with its own regression.
They are not ranked by fix order; sections 1-10 are the ones where an ordinary
contract over ordinary C is certified while false, with no unusual tactics.

## What was found

34 reproductions were rebuilt from scratch and re-run against the release
binary immediately before this file was written; every one exits 0 while
stating a claim that is false under C11/C17 on the LP64 profile Click
documents. They collapse into 24 root causes: 10 critical, 11 high, 3 medium.

The proof core came out clean. Reviewers assigned to the simple tactics, the
persistent fact store, branch joins and splits, order reasoning, and the
`prove_int32_*` axioms produced no reproducible finding. So did direct probes
of the integer operators, control flow, constant-index undefined behaviour,
frame checks on globals, aliasing against `owns`, symbolic float comparison,
and incremental selection after seven kinds of edit (see "Checked and sound"
at the end). The unsoundness is concentrated at boundaries: what a function
may assume at entry, what a call may assume about its callee, how memory
cells are keyed, how literals are typed, and how a loop proof names program
points.

## Reproducing

Each regression below is a self-contained pair. Write the files into an empty
directory and run:

```sh
click verify --time-limit 30s t.click
```

Exit 0 is the bug: the sidecar states something false about the C. Every
regression is intended to land as an mdtest whose `expect` block is a
rejection, so the diagnostic in the acceptance criteria is a shape, not an
exact string. A generator that rebuilds and runs all of them lives in this
review's scratch notes; it is not checked in, because the intended home for
each case is `mdtests/`.

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
- Choose one of: treat an absent effect clause as unbounded havoc, or refuse
  to install a verified rule for a function whose contract has no effect
  clause. Whichever is chosen, document it in the contract reference next to
  `immutable`/`mutable`, since it changes what an omitted clause means.

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

## 5. By-value struct postconditions land on the caller's object

**Severity: critical.** The callee is certified against its own copy, and the
resulting fact is applied to the caller's object, producing a contradictory
state in which anything verifies.

**Violated invariant.** A by-value parameter is a callee-local object. Its
post-state is not observable by the caller, so no `ensures` about it may be
instantiated on the caller's argument.

**Mechanism.** Aggregate parameter binding copies the argument into a fresh
block for the callee, but ensures instantiation maps the parameter back to the
caller's object (`src/kernel/functions.rs`, aggregate binding and the ensures
substitution that follows).

**Regression** (`mdtests/by_value_struct_param_ensures_rejected.md`):

```c
struct pair {
    int32 first;
    int32 second;
};

int32 bump(struct pair value) {
    value.first = 5;
    return value.first;
}

int32 call_bump() {
    struct pair original;
    int32 r;
    original.first = 4;
    original.second = 0;
    r = bump(original);
    return original.first;
}
```

```click
verifying "t.c";

int32 bump(struct pair value) {
    ensures value.first == 5;
}

int32 call_bump() {
    ensures result == 999;
}
```

`call_bump` returns 4. The absurd `result == 999` verifies because the caller's
state has both `original.first == 4` and `original.first == 5`.

**Acceptance criteria.**
- `call_bump`'s claim is rejected, and so is any other value: after the call
  the only provable fact about `original.first` is that it is still 4.
- Either bind by-value aggregate parameters to fresh blocks on the caller side
  of instantiation too, or reject post-state mentions of a by-value parameter
  in `ensures` and expose only `old(value.field)`. If the latter, the
  diagnostic must say which clause is at fault.
- `mdtests/struct_by_value_scalar_copy.md` and the rest of the by-value family
  still pass.

---

## 6. A reversed range consume splits ownership into overlapping residues

**Fixed** in `Reject consuming a reversed memory range`; the regression is
`mdtests/reversed_range_consume_rejected.md`. Kept here until the next
section split, since the guard audit below is still open.


**Severity: critical.** A callee that consumes `p[lo..hi]` with `lo > hi`
leaves the caller holding two owned ranges that overlap. Distinct owned facts
are assumed disjoint, so a store through one no longer invalidates a load
through the other.

**Violated invariant.** Splitting an owned range must preserve disjointness of
the residues. An empty or reversed range consumes nothing.

**Mechanism.** The range split on consume in
`src/kernel/primitives/resource_algebra.rs` computes the residues as
`[start..lo]` and `[hi..end]` without requiring `lo <= hi`.

**Regression** (`mdtests/reversed_range_consume_rejected.md`):

```c
int32 g(int32* p, int32 lo, int32 hi) {
    return 0;
}

int32 t(int32* p, int32 lo, int32 hi) {
    int32 x;
    int32 r;
    r = g(p, lo, hi);
    x = p[0];
    p[hi] = 7;
    return x;
}
```

```click
verifying "t.c";

int32 g(int32* p, int32 lo, int32 hi) {
    consumes p[lo..hi];
}

int32 t(int32* p, int32 lo, int32 hi) {
    requires 1 <= lo;
    requires lo <= 10;
    requires 0 <= hi;
    requires hi <= 9;
    consumes p[0..10];

    ensures result == p[0];
}
```

With `lo = 1, hi = 0` the residues are `owns p[0..1]` and `owns p[0..10]`,
which overlap. `x` is read before `p[hi] = 7` writes the same cell, so the
postcondition asserts `3 == 7` for an entry state with `p[0] == 3`.

**Acceptance criteria.**
- The sidecar is rejected. Either the call fails because `lo <= hi` is not
  established, or the split leaves the holder intact and the postcondition then
  fails on the store.
- A positive mdtest keeps an ordinary `lo <= hi` split working.
- Check the same guard on the other range operations in the algebra
  (`contains`, `separate`, merge) rather than only on consume.

---

## 7. The pure-function `decreases` check is name-based and scope-blind

**Severity: critical.** A `let`, fold, or match binder that shadows the measure
parameter satisfies the descent check, so an inconsistent pure definition is
accepted and its equations leak into C claims.

**Violated invariant.** A recursive pure function is admitted only when every
recursive call strictly decreases the declared measure. The measure names a
parameter; a shadowing binder is a different variable.

**Mechanism.** `validate_recursive_call_edge`
(`src/surface/validation/expression_analysis.rs:919-970`) matches the
decreasing argument syntactically, by variable name, against the measure
parameter name, and looks its bound up in a name-keyed `lower_bounds` map. No
binder scoping is applied on the way down through
`validate_recursive_calls_in_expression`.

**Regression** (`mdtests/pure_decreases_shadowed_binder_rejected.md`):

```c
int32 never_one(int32 x) {
    if (x == x + 2) {
        return 1;
    }
    return 0;
}
```

```click
verifying "t.c";

function bad(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { (2..3).fold(0, |acc, n| acc + bad(n - 1) + 2) }
}

theorem t(x: int32) {
    requires x == bad(1);
    ensures x == x + 2 by {
        unfold(bad(1));
        simp();
    }
}

int32 never_one(int32 x) {
    requires x == bad(1);
    requires x < 100;
    ensures result == 1 by {
        execute();
        apply(t(x));
        have 0 == 1 by {
            contradiction(x == x + 2);
        }
        simp();
    }
}
```

The fold binder `n` shadows the parameter, so `bad(n - 1)` is `bad(1)` and the
definition unfolds to `bad(1) == bad(1) + 2`, which no `int32` satisfies.
`never_one` returns 0 for every input.

**Acceptance criteria.**
- The definition of `bad` is rejected at declaration validation, with a
  diagnostic naming the shadowing binder, so the theorem and the C claim never
  get a chance to be checked.
- Resolve the measure through binder scopes rather than by name; alpha-renaming
  the fold binder must not change the verdict.
- Cover all three binder forms in the regression: `let`, fold item, and match
  arm. Recursive definitions that genuinely descend still verify
  (`mdtests/pure_function_unfold.md`, `pure_induction_countdown.md`).

---

## 8. Floating-point constant folding is wrong in four distinct ways

**Severity: critical.** The integer-space IEEE evaluator gets mixed-sign
`float` comparison, cancellation, widening, and out-of-range conversion wrong.
Each yields a verified false claim about a program with no symbolic inputs.

**Violated invariant.** Constant folding agrees with IEEE-754 at the declared
width: comparison is a total order on non-NaN values, an exactly representable
result is exact, widening `float` to `double` preserves the value including
infinities, and a float-to-integer conversion out of range is undefined
behaviour rather than a value.

**Mechanism.** `src/kernel/primitives/term_operations.rs`, the `DecodedFloat`
evaluator and `compare_float_bits`. The comparison defect is `float32`-only;
`double` comparison is correct.

**Regression A**, inverted mixed-sign `float` comparison
(`mdtests/float32_mixed_sign_compare_rejected.md`):

```c
int32 f32lt() {
    float a = -1.0f;
    float b = 1.0f;
    if (a < b) {
        return 1;
    }
    return 0;
}
```

```click
verifying "t.c";

int32 f32lt() {
    ensures result == 0;
}
```

`-1.0f < 1.0f` is true, so the function returns 1. Click also certifies the
mirror claim that `-1.0f > 1.0f`.

**Regression B**, cancellation
(`mdtests/float_cancellation_folding_rejected.md`):

```c
int32 cancel() {
    double x = 1.0 - 0.96875;
    if (x == 0.03125) {
        return 1;
    }
    return 0;
}
```

```click
verifying "t.c";

int32 cancel() {
    ensures result == 0;
}
```

All three values are exactly representable in binary64 and the subtraction is
exact, so the function returns 1.

**Regression C**, widening (`mdtests/float_widen_infinity_rejected.md`):

```c
int32 widen() {
    float f = INFINITYF;
    double d = (double) f;
    if (isnan(d)) {
        return 1;
    }
    return 0;
}
```

```click
verifying "t.c";

int32 widen() {
    ensures result == 1;
}
```

Widening infinity yields infinity, not NaN, so the function returns 0.

**Regression D**, out-of-range conversion: `(int32) 3.4e38` folds to 0 instead
of being reported as undefined behaviour. A fifth, lower-severity case is
mis-rounded subnormal division.

**Acceptance criteria.**
- All four regressions are rejected, and the corresponding true claims verify.
- Add a differential test over a fixed vector of bit patterns (signed zeros,
  subnormals, infinities, NaNs, cancellation pairs, boundary conversions)
  comparing the evaluator against known-good expected values, so the next
  encoding change cannot silently regress.
- The float mdtests already in the tree continue to pass.

---

## 9. `at(L.entry, ...)` denotes two different states in one loop proof

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

## 10. The `calloc` zeroed flag survives a callee's writes

**Severity: critical.** Call havoc clears cells but not the allocation's
zeroed status, so a caller reads 0 from memory the callee overwrote.

**Violated invariant.** "This allocation reads as zero where unwritten" is
invalidated by any write the caller cannot see, exactly like a cell value.

**Mechanism.** The zeroed-allocation tables in
`src/kernel/primitives/memory_state.rs` (`zeroed_allocations`,
`zeroed_prefix_allocations`) are carried across `with_call_memory_havoc`
unchanged.

**Regression** (`mdtests/calloc_zeroed_survives_call_rejected.md`), two C
files plus the sidecar:

```c
/* fill.c */
void fill(int32* p) {
    p[0] = 5;
}
```

```c
/* t.c */
int32 t() {
    int32* p = calloc(1, sizeof(int32));
    if (p == 0) {
        return 0;
    }
    fill(p);
    int32 r = p[0];
    free(p);
    return r;
}
```

```click
verifying "fill.c";
verifying "t.c";

void fill(int32* p) {
    owns p[0..1];
    mutable p[0..1];
}

int32 t() {
    ensures result == 0;
}
```

`t()` returns 5.

**Acceptance criteria.**
- The sidecar is rejected; with `ensures p[0] == 5;` added to `fill`, the true
  claim `result == 5` verifies.
- Loop havoc gets the same treatment: a loop body that stores into a
  `calloc`'d block must not leave the block readable as zero afterwards. One
  regression each.
- `mdtests/realloc_preserves_calloc_prefix.md` and the other zeroed-allocation
  tests still pass.

---

## 11. Sidecar integer literals in [2^31, 2^32) wrap to negative `int32`

**Severity: high.** A spec author writing an ordinary unsigned constant gets a
different number than they wrote, and the C frontend disagrees with the sidecar
about the same digits.

**Violated invariant.** A literal in a sidecar denotes the value written.

**Mechanism.** The unsuffixed decimal branch of the sidecar tokenizer
(`src/surface/parser/tokenizer.rs:253-262`) emits `Token::Number(u32)` for
anything that fits `u32`, and only values above `u32::MAX` become
`Int64Number`/`UInt64Number`. `src/surface/parser.rs:4610` turns that token
into `CValue::Int32(Constant(value))` and `:4920` into
`C0Expression::Int32Literal(value)` — the raw 32-bit pattern read as signed.
The C frontend types the same digits as `int64`.

**Regression** (`mdtests/sidecar_literal_wraps_rejected.md`):

```c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "t.c";

int32 identity(int32 x) {
    requires x == -2147483648;
    ensures result == 2147483648;
}
```

`-2147483648 == 2147483648` is false; the sidecar verifies because both
literals become the same `int32` bit pattern.

**Acceptance criteria.**
- The sidecar is rejected, either as a type error or as an unproved claim.
- Literals above `INT32_MAX` are typed as the C frontend types them, so
  `ensures result == 4294967295` cannot be proved of a function returning `-1`.
- Comparisons that mix widths after the change are either well-typed or
  rejected with a source-positioned diagnostic; silent reinterpretation is what
  this bug is.

---

## 12. Literal and operator typing: `sizeof`, negated literals, `?:`

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

## 13. Uninitialized reads missed via symbolic index, callee, block re-entry

**Severity: high.** Four findings. Reading indeterminate automatic storage is
undefined behaviour that Click claims to check, and these paths do not.

**Violated invariant.** A load from automatic storage that was never written is
undefined behaviour, whatever the index expression looks like and whoever
performs the load.

**Mechanism.** The stack-local check in
`src/kernel/eval/memory_loads.rs:515-524` fires only when no possibly-aliasing
cell matched, which needs a concrete offset; heap blocks have an explicit
`uninitialized_allocations` table and are handled correctly. Nothing carries
initialization state across a `views`/`owns` transfer at a call, and
block-scoped objects reuse one block for the whole function.

**Regression A**, symbolic index
(`mdtests/uninit_local_symbolic_index_rejected.md`):

```c
int32 local_sym(int32 i) {
    int32 a[3];
    a[0] = 1;
    a[1] = 2;
    return a[i];
}
```

```click
verifying "t.c";

int32 local_sym(int32 i) {
    requires i == 2;
    ensures result == result;
}
```

`a[2]` was never written. With the index spelled as the constant `2` the same
read is correctly rejected.

**Regression B**, through a callee
(`mdtests/uninit_through_callee_views_rejected.md`):

```c
int32 same_twice(int32* p) {
    return p[0] == p[0];
}

int32 uninit_eq_callee() {
    int32 x;
    return same_twice(&x);
}
```

```click
verifying "t.c";

int32 same_twice(int32* p) {
    views p[0..1];
    immutable;
    ensures result == 1 by auto;
}

int32 uninit_eq_callee() {
    ensures result == 1 by auto;
}
```

**Regression C**, a `views` range wider than the caller's block
(`mdtests/views_exceeds_local_block_rejected.md`):

```c
int32 g(int32* a) {
    return a[2];
}

int32 f() {
    int32 b[2];
    int32 c = 9;
    b[0] = 1;
    b[1] = 2;
    return g(b) * 0 + c;
}
```

```click
verifying "t.c";

int32 g(int32* a) {
    views a[0..3];
    ensures result == a[2];
}

int32 f() {
    ensures result == 9;
}
```

`f` passes a two-element array where the callee's precondition claims three.

**Regression D**, block-scoped storage
(`mdtests/block_local_stale_across_iterations_rejected.md`):

```c
int32 f() {
    int32 i;
    for (i = 0; i < 2; i++) {
        int32 a[2];
        if (i == 1) {
            return a[0];
        }
        a[0] = 5;
    }
    return 0;
}
```

```click
verifying "t.c";

int32 f() {
    ensures result == 5;
}
```

`a` is a fresh object each iteration, so the second iteration reads
indeterminate storage.

**Acceptance criteria.**
- Each regression is rejected with a "read of uninitialized storage"
  diagnostic (C) or a failed precondition (C's `views` case).
- Track initialization for stack blocks the way heap blocks are tracked, so a
  symbolic index into a partly initialized array is checked against what was
  actually written.
- Check `views`/`owns` preconditions at a call against the callee's block
  extent and its initialization state.
- Give block-scoped objects a fresh block per entry to the block.

---

## 14. String literal storage can be made writable through a contract

**Severity: high.** A callee contract that takes `owns` over a literal's
storage lets the caller store into read-only memory with no diagnostic.

**Violated invariant.** Modifying a string literal is undefined behaviour
(C11 6.4.5p7). Read-only backing storage stays read-only across resource
transfer.

**Mechanism.** `initialize_c_function_globals` installs the literal's block
with `with_read_only_block` and then unconditionally grants an `own_memory`
resource over it (`src/kernel/functions.rs:3006-3040`); the ownership is what
a callee's `mutable` clause then consumes.

**Regression** (`mdtests/string_literal_writable_rejected.md`):

```c
void setb(uint8 *p) {
    p[0] = 1;
}

int32 t() {
    uint8 *s = "ab";
    setb(s);
    return s[0];
}
```

```click
verifying "t.c";

void setb(uint8 *p) {
    owns p[0..1];
    mutable p[0..1];
    ensures p[0] == 1;
} by { execute(); frame(); simp(); }

int32 t() {
    ensures result == 1;
} by { execute(); simp(); }
```

**Acceptance criteria.**
- Passing literal storage to a parameter that requires `owns` is rejected, or
  the store inside `setb` fails against the read-only block. Either way the
  sidecar does not verify.
- `mdtests/string_literals_reject_write.md` (the direct-store case) still
  passes, and reading a literal through a `views` contract still works.
- The variant where the literal is returned from a helper that declares
  `produces result[0..3]` is the same bug and gets the same treatment.

---

## 15. A store through `&local` in an inline header helper is dropped

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

## 16. A reloaded pointer to a local is treated as a distinct block

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

## 17. `--changed-since` misses named-contract and algebraic-type changes

**Severity: high.** After a shared `contract` block is weakened, every function
is reused and the run exits 0, while a full verify of the same tree fails.

**Violated invariant.** Incremental selection re-verifies every claim whose
meaning could have changed. Shared definitions that participate in a proof are
part of that set.

**Mechanism.** `shared_environment_changed`
(`src/surface/verification.rs:329-334`) compares predicate, Click pure
function, resource, and theorem definitions. Named function-contract
definitions and `spec enum` algebraic types are not compared, and a function
block that references a contract by name is byte-identical before and after,
so nothing pulls it in through the reverse call graph.

**Regression** (`mdtests/` cannot express this; it needs a git baseline, so it
belongs in `tests/` beside the other incremental tests, or as a CLI test). The
procedure:

1. Take `mdtests/c_named_function_contract.md`'s sources as three C files and
   one sidecar with a `contract int32 Comparator(...)` whose `ensures` is
   `result == left - right`. Commit.
2. `click verify t.click` — passes, records the baseline marker.
3. Weaken the contract's `ensures` to `result >= 0`. Commit.
4. `click verify --changed-since <first commit> t.click` — prints
   `selected (0): (none)`, `reused (3): apply, caller, compare`, exit 0.
5. `click verify t.click` on the same tree — fails, `apply.ensures_0`
   unproved.

**Acceptance criteria.**
- Step 4 selects `apply` (at least) and fails exactly as step 5 does.
- `contract_definitions()` and algebraic type definitions join the
  shared-environment comparison; add each to the regression.
- Audit the rest of the file-level declaration kinds against that comparison in
  the same change, and note in `docs/reference/cli/verify.md` that any shared
  declaration change forces a rebuild.

---

## 18. Termination resolves calls by name and drops nested-loop writes

**Severity: high.** Two independent holes in the same judgment; both certify
`decreases` for a program that does not terminate.

**Violated invariant.** Termination evidence covers the calls the program
actually makes, under the scoping C gives them, and a measure variable written
anywhere in the loop body is not assumed unchanged.

**Mechanism.** `src/kernel/termination.rs` resolves an indirect call by the
callee's name, so a parameter that shadows a file-scope function of the same
name resolves to the file-scope function. Separately, when a nested loop writes
a variable named by the enclosing measure, the checker removes the alias
instead of making the value fresh.

**Regression A**, shadowed callback
(`mdtests/termination_shadowed_callback_rejected.md`):

```c
int32 helper(int32 x) {
    return 1;
}

int32 spin(int32 x) {
    if (x > 0) {
        return spin(x);
    }
    return 1;
}

int32 f(int32 (*helper)(int32), int32 n) {
    if (n > 0) {
        return f(helper, n - 1);
    }
    return helper(1);
}

int32 caller(int32 n) {
    if (n > 0) {
        return caller(n - 1);
    }
    return f(&spin, 0);
}
```

```click
verifying "t.c";

contract int32 One(int32 x) {
    ensures result == 1;
}

int32 helper(int32 x) {
    ensures result == 1;
}

int32 spin(int32 x) {
    ensures result == 1;
}

int32 f(int32 (*helper)(int32), int32 n) {
    decreases n;
    requires One(helper);
    ensures result == 1;
}

int32 caller(int32 n) {
    decreases n;
    ensures result == 1;
}
```

C11 6.2.1p4: the parameter hides the file-scope `helper`, so `helper(1)` calls
`spin`, which recurses on the same argument forever. `caller(0)` never returns,
yet its `decreases n` is certified. Note that frame checking resolves the same
shadowing correctly, so this is specific to termination.

**Regression B**, nested loop writing the measure
(`mdtests/nested_loop_measure_rejected.md`):

```c
int32 nest(int32 n) {
    while (n > 0) {
        while (n < 10) {
            n = n + 1;
        }
        n = n - 1;
    }
    return n;
}
```

```click
verifying "t.c";

int32 nest(int32 n) {
    requires n >= 0 and n <= 100;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0 and n <= 100;
        preserve by {
            loop {
                decreases 10 - n;
                invariant n >= 0 and n <= 100;
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

For any `0 < n <= 100` the inner loop raises `n` to 10 and the outer body
lowers it to 9, forever. Replacing the trailing `n = n - 1` with `n = n + 1` is
correctly rejected, which shows the checker runs and this case slips past it.

**Acceptance criteria.**
- Both `decreases` clauses are rejected.
- Resolve indirect calls through the scoped binding (parameter before
  file-scope), matching what the partial-correctness path already does.
- Make a variable written by a nested loop fresh at the enclosing back edge
  rather than dropping its alias.
- `mdtests/c_decreases_loop.md`, `c_decreases_lexicographic_loop.md`, and the
  structural-measure tests still pass.

---

## 19. `mutable &obj.field` on a static struct lowers to the first cell

**Severity: high.** A footprint that names one field authorizes writes to a
different field.

**Violated invariant.** A field place in an effect clause denotes that field's
bytes, at its ABI offset.

**Mechanism.** Address-of field footprint lowering for aggregate globals drops
the field offset (`src/surface/lowering/annotations.rs`, the `AddressOf` path
for global objects around `:2368-2380`).

**Regression** (`mdtests/static_field_footprint_rejected.md`):

```c
struct pair {
    int32 first;
    int32 second;
};

struct pair gs;

int32 f() {
    gs.first = 9;
    return 0;
}
```

```click
verifying "t.c";

int32 f() {
    mutable &gs.second;
    ensures result == 0;
}
```

**Acceptance criteria.**
- The sidecar is rejected: writing `gs.first` is outside a footprint that names
  `gs.second`.
- `mutable &gs.first;` verifies, and `mdtests/aggregate_static_effect.md` still
  passes.
- Cover a nested field (`&gs.inner.value`) in the regression too, since the
  offset composition is the thing being fixed.

---

## 20. Aggregate copies skip fields and copy uninitialized sources

**Severity: high.** A whole-struct assignment leaves the destination's previous
value in fields the copy does not handle.

**Violated invariant.** Struct assignment copies every member (C11 6.5.16.1p2),
and copying from an uninitialized source is a read of indeterminate storage.

**Mechanism.** `copy_aggregate_fields` (`src/kernel/functions.rs:3526-3549`)
matches a fixed list of field types and ends with `_ => continue`, so
`float*`, float arrays, and other unlisted types are silently skipped. The
frontend routes union-containing layouts through this kernel copy
(`C0Statement::AggregateCopy`, executed at
`src/kernel/eval/statements.rs:568`), which is how the skip becomes reachable.

**Regression** (`mdtests/aggregate_copy_skips_field_rejected.md`):

```c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
    float* fp;
};

int32 stale_union_copy(struct packet* src) {
    float arr[1];
    struct packet dst;
    dst.tag = 1;
    dst.fp = arr;
    dst = *src;
    return dst.tag * 10 + (dst.fp == 0);
}
```

```click
verifying "t.c";

int32 stale_union_copy(struct packet* src) {
    requires loadable(src->tag);
    requires loadable(src->payload.number);
    requires loadable(src->fp);
    requires src->tag == 2;
    requires src->fp == 0;
    consumes src->tag;
    consumes src->payload.number;
    consumes src->fp;
    ensures result == 20;
    produces src->tag;
    produces src->payload.number;
    produces src->fp;
}
```

After the copy `dst.fp` is null, so the function returns 21, not 20.

**Acceptance criteria.**
- The sidecar is rejected and `ensures result == 21` verifies.
- Replace the catch-all `continue` with either a complete match over modeled
  leaf types or an explicit unsupported-layout error; a silently skipped field
  must be impossible.
- A copy whose source leaf is uninitialized reports a read of uninitialized
  storage rather than keeping the destination's old value.

---

## 21. `continue` in a `switch` inside a `do ... while` with a call condition

**Severity: high.** The `continue` is lowered as a `switch` break, so the rest
of the body runs and the loop condition is not reached as C requires.

**Violated invariant.** `continue` always continues the innermost enclosing
loop, never the enclosing `switch`.

**Mechanism.** `prepend_condition_check_before_loop_continues`
(`src/languages/c/syntax.rs:13400`) rewrites `continue` for the
call-in-condition form without distinguishing it from a `switch` `break`.

**Regression** (`mdtests/do_while_switch_continue_rejected.md`):

```c
int32 stop_now() {
    return 0;
}

int32 dw_switch() {
    int32 count = 0;
    int32 tail = 0;
    do {
        count++;
        switch (count) {
            case 1:
                continue;
            default:
                break;
        }
        tail++;
    } while (stop_now());
    return tail;
}
```

```click
verifying "t.c";

int32 stop_now() {
    ensures result == 0;
}

int32 dw_switch() {
    ensures result == 1;
}
```

The `continue` skips `tail++` and goes to the post-test, which is false, so
the function returns 0.

**Acceptance criteria.**
- The sidecar is rejected and `ensures result == 0` verifies.
- Cover `while`, `for`, and `do ... while`, each with a `continue` inside a
  `switch`, with and without a call in the loop condition.

---

## 22. Range byte counts wrap modulo 2^32

**Severity: medium.** A huge or negative element range lowers to a tiny byte
footprint, so a `loadable` fact is certified for memory that was never claimed.

**Violated invariant.** The byte footprint of an element range is
`(end - start) * element_width` without wrapping.

**Mechanism.** `CMemoryRange::byte_footprint`
(`src/kernel/primitives/contracts.rs:1197`) multiplies with the ordinary
32-bit `Bitvector32Term::multiply` and emits no overflow obligation.

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
- Fold this into section 6's guard audit: both are range arithmetic without
  side conditions.

---

## 23. Intra-object array overflow is modeled as a flat access

**Severity: medium** (documented, but it accepts undefined behaviour).

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

## 24. Symbolic specification arithmetic wraps where constants are undefined

**Severity: medium.** No false non-reflexive claim was found, but the two
halves of the specification language disagree, which is how the next hole gets
in.

**Violated invariant.** `docs/concepts/c0-and-c-fragments.md` says a C fragment
in a specification follows C0 integer rules "including signed-overflow
obligations". Symbolic spec terms do not produce them.

**Mechanism.** `evaluate_spec_int32_binary_paths` (`src/kernel/spec.rs:3137`)
drops undefined-behaviour outcomes with
`filter_map(c_expression_path_value)`, so a symbolic overflowing term becomes a
wrapping bitvector term with no obligation. The same expression with constant
operands fails to lower at all ("produced 0 paths, not one").

**Regression** (`mdtests/spec_symbolic_overflow_wraps.md` — the expectation
depends on the resolution):

```c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "t.c";

int32 identity(int32 x) {
    ensures (x + 1) - 1 == x;
}
```

Verifies today with no `requires`. The concrete
`ensures (2147483647 + 1) - (2147483647 + 1) == 0;` fails to lower, and
`ensures x + 1 > x;` correctly fails.

**Acceptance criteria.**
- Pick one semantics and make both halves agree: either emit `defined(...)`
  obligations for symbolic specification arithmetic so this sidecar needs
  `requires x < 2147483647`, or document specification arithmetic as wrapping
  and make the constant case fold rather than fail to lower.
- Whichever is chosen, the diagnostic for the constant case stops being
  "the kernel lowering produced 0 paths, not one", which is an internal shape
  leaking into a user-facing message.

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

## Reported but not verified

These came out of the review without an independent reproduction, because the
run hit its usage limit before their verification agents ran. They are recorded
so the leads are not lost; confirm each before acting on it.

- A postcondition may read the storage of a local whose address is returned.
- Overlapping struct self-assignment `*p = *q` gets a definite sequential
  field-copy result where C leaves it undefined.
- Two identical string literals are proved distinct; a freed pointer is proved
  unequal to a later fresh allocation. Both are unspecified in C, so proving
  either direction is wrong.
- Null pointer arithmetic `(int32*)0 + 1` is accepted and yields a definite
  non-null pointer.
- A variable declared in a `for` initializer stays readable after the loop.
- Contract-side `==` between a `uint64` result and an `int32` value compares
  after an implicit conversion instead of rejecting the mismatch.
- A contract naming `&c[0..1]` resolves to a file-scope global while the C body
  means a function-local static of the same name.
- Relational comparison of two unrelated pointer parameters is accepted with no
  same-object obligation.
- A single call inside an expression is sequenced before sibling operand loads,
  fixing one of C's permitted evaluation orders.
- Symbolic 64-bit signed addition and multiplication are reported as definite
  overflow (a false rejection, not a false acceptance).
- Nested field designator followed by a positional initializer continues at the
  wrong nesting level.

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
  shadowing a file-scope function (frame checking resolves the shadowing
  correctly — only termination does not; see section 18).
- Resources: two `owns` clauses over aliasing arguments are rejected as
  overlapping; `views` and `owns` over the same cell are not assumed separate.
- Floating point with symbolic operands: NaN keeps the third path in
  `a < b` / `b <= a`, `a == a` is not assumed, `a != a` is not assumed false.
- Undefined behaviour inside `requires` is checked as a callee precondition at
  call sites, and an overflowing callee `ensures` instantiation yields no fact.
- Incremental selection re-verifies correctly after a callee contract change, a
  callee body change, a strengthened callee precondition, a caller body change,
  a global initializer change, an extern contract change, and a theorem change
  (the gap is only the shared-declaration kinds in section 17).
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

## Provenance

Produced on 2026-09-06 against `d6502258` by sixteen subsystem reviewers and
six black-box attackers, each finding then rebuilt by an independent
reproducer and challenged by an adversarial skeptic. 89 findings were reported;
72 had the false claim re-run and accepted, 59 of those also cleared both
verification passes, and 4 were refuted (listed above). The 34 regressions in
this file were rebuilt from scratch and re-run immediately before it was
written. No fix has been attempted, and the tree is otherwise untouched.
