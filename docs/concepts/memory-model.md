# Memory model

This page describes how Click models C memory: blocks and pointers, the byte
view of integer cells, heap lifetimes, argument aliasing, viewable ranges, old
memory, write footprints, stack memory, and Click array refs.

The memory model is central to Click. Many proof failures are aliasing or frame
failures, not arithmetic failures.

## Program points, symbolic states, and version points

These names describe different things:

- A **program point** identifies where an expression is evaluated. It is the
  first argument of `at(point, expression)`, such as `region(3).exit`.
  A proof mark names the current point on its proof path. The surface type
  `ProgramPointSelector` distinguishes code locations from proof marks.
- A **recorded symbolic state** is the verifier's `ExecutionState` retained
  for a point on one proof path. It contains symbolic locals, memory,
  resources, and execution bookkeeping. `RecordedStates` associates point
  selectors with these states. It is not a table of all concrete values at
  a source location, and different paths need not supply one common state.
- A **memory state** is a `Memory` value, or its interned `SharedMemory`
  handle. It records symbolic memory information, which may be incomplete,
  abstracted by a call or loop, or projected for one selected read. It is
  not a program point or a complete execution state.
- A **version point** identifies the memory state selected by the
  assumption-free version walk for a particular cell or observed block.
  The kernel resource tracker represents it with `VersionPoint`. A read's
  address, type, and version point determine its identity.

Evaluating a read at a later program point can select an earlier version
point when the intervening operations leave that cell unchanged. Two
program points can therefore name the same read without being the same
program point. A version point need not have a direct surface name; raising
uses a program point whose recorded state selects that exact read.

Use these terms in code, comments, diagnostics, and documentation. A model
field's version is its symbolic value; comparing it uses a borrowed
`StatePoint`, rather than inventing a memory version point for the field.

## Blocks and pointers

Kernel memory is a map of named byte-sized blocks plus known cells. A
pointer is a semantic object:

```text
Pointer { block, offset }
```

These coordinates describe the raw address. A complete C pointer separately
carries its designation and selected subobject extent. Numeric address equality
does not equate those bounds. C pointer arithmetic is scaled by the pointee
type: `int32*` adds four bytes per element, while `uint8*` adds one byte per
element.

Click's integer constant `0` converts to a single canonical null pointer in
pointer-valued return, initialization, assignment, argument, and comparison
contexts. Implicit integer-to-pointer conversions accept only zero.

Under the LP64 profile an object pointer has a 64-bit integer representation.
A pointer-to-integer cast retains the complete pointer, including its selected
subobject bounds, beside its numeric address. `address(p)` observes only that
address. Whole local, store/reload and aggregate copies retain a representation;
ordinary arithmetic, changes of integer format and partial overwrites discard
it. A lossless cast back preserves the selected bounds, including when the
target is `void*` or a character pointer. It does not apply the widening rule
for a direct pointer-to-pointer byte/void cast. Casts between character-pointer
types and compiler-inserted pointer conversions retain the existing view,
including its bounds. An explicit conversion from a non-character pointer to
a character pointer, or any explicit cast to `void*`, selects the enclosing
object's view.

C pointer comparisons state only numeric address equality. Equal addresses do
not make equal pointer values or transfer bounds: one object's one-past address
can coincide with another object's first element. Comparison with null is exact;
null converts to integer zero, and a 64-bit word proven zero converts to the
canonical null pointer, including after clearing tag bits.

Incoming C words, opaque modular results and complete typed word reads have
independent opaque carrier identities. Numeric equality never identifies those
carriers or supplies pointer bounds. A complete word can name an opaque pointer
without granting allocation or access authority. An explicit contract can state
the full relationship using existing cast syntax:

<!-- verified-example: mdtests/a_cast_contract_preserves_an_incoming_packed_pointer.md -->
```click
requires ((word & ~1) as (struct node *)) == p;
```

This equality includes designation and selected extent. It lets a copied word
reconstruct `p` with those bounds. A modular callee must explicitly preserve
such a relationship when callers need it; `ensures result == word` preserves
only the number. Mathematical integers, integer model fields and pure numeric
function arguments carry no C representation.

Numeric tag arithmetic remains a separate theory. Checked low-bit additions,
sets and clears on retained pointer representations keep their source pointer.
Mask identities require the corresponding alignment and tag bounds; casting
back requires the tag cleared. Incoming opaque words retain their identity
through low-bit masks; newly set tag bits must be cleared before a cast can use
the retained carrier. An address equation such as `(word & ~3) == address(p)`
can recover numeric coordinates, but does not establish the full relationship
or authorize a dereference. Clearing a word known to contain only tag bits
recovers the unique null pointer.

See [integer representation policy](https://github.com/clicklang/click/blob/master/design/pointer-integer-representations.md)
for implementation details and remaining Phase B work.

Alignment is evidence, not a property of the pointee type. `aligned(p, n)`
holds when the address of `p` is a multiple of `n`; Click derives it from a
heap allocation (16 bytes), from taking the address of a declared scalar
local (its type's alignment), or from an explicit contract or resource fact,
and it propagates through constant byte displacements. See the language reference
for the proposition.

For `int32**` and `uint8**`, pointer arithmetic advances by the eight-byte
ABI width of each pointer-valued cell.

Memory diagnostics use these same source units. A refused scalar store names
the ownership for its actual width: a one-byte store to `uint8* s` at index
zero requires `owns s[0]`, not four bytes. See the
[byte-store refusal fixture](https://github.com/clicklang/click/blob/master/mdtests/viewed_byte_store_at_index_0.md).
A struct range covering whole
fields names them, for example `{p->left, p->right}`; an embedded field keeps
its dotted path. A range that cannot be expressed as whole source elements
uses an explicit byte cast, such as `((char *)p)[4..12]`. A coverage note that
compares byte offsets says so, and a load in its bounds names the field read,
such as `load(node->right)`.
Branch failures retain source layouts for current pointer locals, including
reassigned parameters and local aliases. A pointer whose source declaration
is unavailable uses explicitly identified byte units.

Pointer arithmetic stays inside the pointed-to object (C11 6.5.6p8): the
result must designate an element of the object or the position one past its
end. For a block whose extent the kernel records, a local array or a heap
allocation, the displacement is checked against that extent. For a block
whose extent it does not record, which is every pointer parameter and every
symbolic or loaded pointer, the ranges the state holds in that block are the
extent it knows: forming `p + k` owes that the result lies within an `owns`
or `views` range of the object, one-past end included, or inside a `viewable`
extent. A range the facts exclude the result from drops out; when they
exclude it from every held range the formation is refused as pointer
arithmetic that left the object, and when one range is left undecided its
bounds are owed as an obligation on the path where they fail; the normal path
does not assume them. Only a range based in the pointer's own object judges
it, so a range of `p` neither bounds nor refutes `q + i` under an alias
`p == q`. Displacing by zero owes nothing, and
a pointer whose object has no held range owes nothing at formation: the access
through it is what is refused then. Element coordinates are compared with
the range's own element width, so a byte pointer into an `int32` range is
not bounded by that range.

Pointers into distinct objects compare unequal under `==` and `!=`, with one
exception. C11 6.5.9p6 lets a pointer one past the end of an object equal
the start of a different object when the implementation happens to place
the second directly after the first, and the kernel does not model object
placement. A comparison in which one operand may be one past the end of its
object and the other may be the start of a different object is therefore
refused, naming the one-past-the-end operand, rather than decided; when the
facts leave the configuration open, the path in which it holds is owed as a
refused path beside the comparison. Two objects' starts, two pointers into one
object, and comparisons with null are decided as before. The kernel's
objects are nonempty, so a pointer at its object's start is never taken for
its end.

## Byte view of integer cells

Known cells are typed: a store of an `unsigned int` records one four-byte
integer cell, not four bytes. A one-byte C access (`unsigned char` or
`signed char`) at a constant offset that lands inside a wider integer cell at
a constant offset of the same block, including at the cell's own address,
uses the cell's byte representation. That representation depends on the
target's byte order, so the view exists only for a little-endian target;
both selectable targets are. Under little-endian order byte `k` of an integer
value `v` is `(v >> 8k) & 0xFF`:

- A one-byte load reads that byte. An `unsigned char` load reads it as is;
  a `signed char` load reads its sign extension when the byte is a constant
  and is refused when it is symbolic.
- A one-byte cell of one character type reads through the other as the same
  eight bits: a byte has one name, its unsigned value, and a `signed char`
  read is its two's-complement reinterpretation. Plain `char` is one of the
  two, unsigned on the kernel target and signed on the user-space target.
  A constant fact about either read decides the other: `u[0] == 200` gives
  `s[0] == -56`, and `s[0] == 7` gives `u[0] == 7`.
- A one-byte store updates the wider cell in place,
  `(v & ~(0xFF << 8k)) | (b << 8k)`, keeping its type and address. No
  separate one-byte cell is added, so the storage keeps a single description.
  A signed 16- or 64-bit cell is updated only when both its value and the
  byte are constants; otherwise the store forgets the wider cell, as any
  partial overwrite does.

The containing cell is found by a bounded lookup of the at most seven
preceding constant offsets in the accessed block; it does no work for cells
elsewhere in memory. Byte view reads apply to C execution only: a
specification load reads the cells at its version point without it.

The following stay refused. A byte of a pointer cell has no view: its
representation is opaque, so a one-byte read of a copied pointer fails as a
load that does not fit the cell, and a one-byte write forgets the pointer
rather than editing it. Several one-byte cells are never assembled into a
wider integer load. A float or `_Bool` cell, a symbolic offset, and any byte
order other than little-endian have no view either.
`mdtests/byte_representation_buffer_byte_read.md` and
`mdtests/byte_representation_byte_mutation.md` verify reads and a defined
mutation through a `memcpy` buffer;
`mdtests/byte_representation_pointer_bytes_refused.md` and
`mdtests/byte_representation_pointer_byte_write_refused.md` pin the pointer
refusals. The design record for representation copies, the byte view, and the
reinterpretations that stay refused is
[Byte representation](../internals/byte-representation.md).

## Heap blocks and lifetimes

The supported `malloc`, `calloc`, and `realloc` forms have a null outcome and a
successful outcome. Success creates a fresh block identity at offset zero, with either
the exact LP64 size of `struct T`, a verified typed extent such as
`count * 4`, `count * sizeof(uint8)`, or `count * sizeof(struct T)`, or an
arbitrary positive byte extent. Heap identities are not reused within a proof.
Fresh `malloc` bytes are
uninitialized, so ownership permits stores but does not make an unstored cell
readable; successful `calloc` cells read as zero or null until overwritten.
A store over any byte of a cell ends that cell's zero reading, whether the
store is narrower than the load and lies inside it or wider and contains it.
Pointer-array `malloc` uses `count * sizeof(int32*)` or
`count * sizeof(uint8*)` with the eight-byte LP64 pointer stride; pointer cells
are uninitialized until stored, and the complete pointer-array range is
reclaimed by `free`. Matching pointer-array `calloc` uses the same range and
initializes each cell to the canonical null pointer until a store overwrites it.

Initialization is recorded apart from values. Fresh heap bytes, automatic
storage, and memory a contract holds as `uninitialized(p[a..b])` start
uninitialized
([uninitialized owned memory](../reference/language/index.md#uninitialized-owned-memory)),
and a plain `owns`, `views`, or `consumes` clause requires the caller to have
initialized the bytes it lends; a store initializes its bytes, and nothing but
the end of the object's lifetime makes them uninitialized again. A store the
facts cannot place (`a[u] = 7` where `u` may name several elements), a call or
loop havoc, or a join forgets cached values, but the bytes those values
occupied stay initialized, so a later read of them is an initialized value the
facts may leave unknown rather than a read of uninitialized storage. A join,
of a C `if` or of a proof `if` or `match`, keeps a value every incoming path
holds for the same cell, since that is the cell's value whichever path was
taken. It also preserves an uncached read when the recorded paths from every
incoming memory show that its complete byte range is unchanged. This uses the
same checked read-preservation rule as other memory transitions, and does not
require restating the fact in the branch interface. It forgets the rest
(`mdtests/a_join_keeps_a_cell_both_arms_agree_on.md`,
`mdtests/a_join_forgets_a_cell_the_arms_disagree_on.md`). It
keeps a byte initialized only when every incoming path initialized it, and a
read at an element index the facts bound (`0 <= i < n`) is initialized when
every element the index may name is. A declaration with an initializer
(`int32 a[4] = {1};`) initializes every byte of its object. Whole-struct
assignment copies a member whose value was forgotten but whose bytes are
initialized as an unknown value, so the destination member is initialized
too; a member nothing wrote is still a read of uninitialized storage. A
successful `realloc` keeps the old block's initialized bytes initialized up
to the new size, and the bytes it grows by start uninitialized.

For a directly admitted initialized input range of complete scalar or pointer
cells, the entry also publishes a pure fact of the form
`forall (k: int32) { lo <= k and k < hi implies defined(p[k]) }`
(or `uint64` for a wide range). The binder ranges over the clause's element
coordinates. Use ordinary `instantiate` with the two bounds to select a read.
Publication constructs one quantified fact per admitted clause; it does not
visit the cells or inspect memory history. The fact describes the entry
state, not every later state. Inactive guarded clauses, `uninitialized(...)`
inputs, and constructor destination storage do not supply it. Aggregate ranges
with padding or multiple cell types do not supply a scalar-array fact.
See [`initialized_input_ranges_publish_definedness.md`](https://github.com/clicklang/click/blob/master/mdtests/initialized_input_ranges_publish_definedness.md),
[`uninitialized_input_does_not_publish_definedness.md`](https://github.com/clicklang/click/blob/master/mdtests/uninitialized_input_does_not_publish_definedness.md),
and [`initialized_input_fact_does_not_survive_free.md`](https://github.com/clicklang/click/blob/master/mdtests/initialized_input_fact_does_not_survive_free.md).

A checked call retains input propositions independently established by the
incoming context's indexed facts and scalar condition checker. Retention does
not repeat memory or ownership derivations, and a pending call obligation
cannot establish its own premise. Retained read terms keep their pre-call
version point; they describe the post-call value only when checked read preservation
connects the two points. See `mdtests/call_checked_input_facts_keep_prestate.md`.

Heap arrays of structs are byte-backed allocations whose indexed member
addresses add `i * sizeof(struct T)` before applying the field offset. This
keeps the allocation extent and field access aligned with the declared ABI,
including structs whose size is not a multiple of four.

A pending `realloc` keeps its old live block and resources in place until the
result is refined. Failure removes only the pending result. Success records a
free edge for the old block, allocates a fresh block, copies the initialized
cells whose complete byte ranges fit in the new extent, and transfers the
complete allocation and memory resources to the fresh block. The old and new
resources use typed logical units when the extents are exactly divisible by
the pointer's element width and byte units otherwise. This applies to every
pointer type `realloc` accepts, listed in
[Heap allocation](../reference/language/c.md#heap-allocation), including raw
byte extents. A partial cell is conservatively not
reintroduced as initialized. For a bounded zeroed `calloc`
source, the successful result also records the preserved zeroed prefix; any
grown tail is uninitialized and is not treated as zero.

Click tracks two different facts on the successful branch:

- owned memory for the complete object permits reads and writes;
- `allocation(p, bytes)` is the exclusive authority and obligation to end that
  allocation's lifetime; `bytes` may be a supported symbolic runtime extent.

`free(p)` requires both facts for the complete allocation and consumes them.
`free(NULL)` changes nothing. An interior, stack, opaque, or already-freed
pointer is not a valid free target. A successful free ends the whole block's
lifetime; all aliases and derived addresses then reject loads and stores, and
a second free is diagnosed separately. Their values are also indeterminate,
so comparing, subtracting, offsetting, truth-testing, or converting such a
pointer to an integer is refused as undefined behavior, while copying,
storing, or overwriting it is not (see
[Undefined behavior](undefined-behavior.md#freed-pointers-are-indeterminate)). Verified function exits also check
that live allocation authority was returned through the contract or freed.

The allocation/null refinement and allocation/free transitions are recorded
as memory-derivation edges. Registering the pending result has an explicit
memory-preserving edge, allowing existing loads and memory resource facts to cross the
unresolved state. Failed allocation removes that metadata and returns to the
pre-allocation memory identity without producing allocation authority.
Successful allocation starts from the pending memory but introduces only
its fresh, uninitialized block. A successful `free` also emits a checked heap
`HeapAllocationFreed` effect connecting the memory before and after it,
exact base, and possibly symbolic byte extent. This is deliberately distinct
from an owned byte range: deallocation changes which allocation identities
are live, while an owned range bounds ordinary stores. Exact contract
checking and modular call verification therefore use the same allocation
model as direct execution without pretending deallocation is a byte write.

Writes to a block freshly allocated by the current function are internal while
that block is being initialized: they do not mutate memory that was externally
visible at function entry. The function must still return the new access and
lifetime authority in its contract or free it. Registering allocation authority
for already-owned storage immediately before a direct `free` is likewise
bookkeeping, while the actual free remains an explicit allocation effect.

## Argument memory and aliasing

Function pointer parameters are modeled as symbolic offsets into one shared
external argument-memory block. The identity of that external block is not
assumed distinct from null, so an unconstrained pointer parameter retains both
its null and non-null executions. Distinct pointer parameter names do not imply
non-aliasing.

If a proof relies on non-overlap, state it:

<!-- verified-example: mdtests/copy_n_segment_invariant.md -->
```click
requires separate(memory(dst[0..n]), memory(src[0..n]));
```

This is intentionally C-like. C functions can be called with aliased pointers
unless their contract rules that out.

Ownership is located by the address it names, not by the spelling that
introduced it. A memory resource is held at a pointer, and two pointers an
*exact* equality proves equal are one address, so where a proof has introduced
ownership through a name the C program does not use — the pointer payload of a
matched resource arm is the case that matters, since it is a fresh symbolic
pointer at any frontier — the arm's clauses are instantiated at the equal
pointer instead. The read, the write, the cell's load identity, the child
resources' arguments, and the body a later `fold` requires then all name the
one address under the program's own spelling. Only an assumed pointer equality
between two blocks does this, read from the index those facts are filed in: a
disequality or a disjunction is not an alias, an equality inside one block is a
`PointerOffsetEqual` that cannot exchange a block at all, and the exchange
never moves an offset. See
[resources](resources.md) for the rule as it appears at `unfold` and `fold`,
`mdtests/binding_cell_read_through_equal_local.md` for the reduction with its
two negatives, and `mdtests/rb_ascending_walk_to_root.md` for the ascending
walk that needs it once per iteration.

## Viewable ranges

Use `viewable` to prove memory safety:

<!-- verified-example: mdtests/viewable_segment_forms.md -->
```click
requires viewable(p[0..3]);
requires viewable(p[0..n]);
requires viewable((p + 1)[0..n - 1]);
```

Segment forms are half-open `int32` element ranges. For `int32 p[]`,
`viewable(p[0..n])` means cells `p[0]` through `p[n - 1]` are available for
four-byte `int32` access. For `uint8 p[]`, the same spelling covers `n`
one-byte elements.

Native `uint64` element ranges preserve their full counts.
A prefix of the suffix at `p + (whole - remaining)` retains read authority
when `remaining <= whole` and the requested extent is at most `remaining`.
The first-byte read additionally requires a positive remaining count; the
native bounds are not replaced by their low words. See
[`native_nonempty_suffix_first_byte.md`](https://github.com/clicklang/click/blob/master/mdtests/native_nonempty_suffix_first_byte.md).

A same-base prefix
can be proved from a held view and an explicitly selected unsigned coverage
bound. For byte elements, `requested <= held` covers the prefix; for wider
elements, compare the complete nonwrapping byte extents as well. The source
view must remain live at the destination point. A low-word bound
supplies no full-width coverage.
A shifted byte subrange additionally needs its exact nonnegative offset to
fit the source extent, and the requested count to fit the source extent
minus that offset. This subtraction guard prevents unsigned wrap from
creating coverage. The query uses structural parent addresses or an explicitly
selected source; it does not scan other ranges in the block.

See [the native prefix fixtures](https://github.com/clicklang/click/blob/master/mdtests/native_view_prefix_narrowing.md)
and [native byte-window fixtures](https://github.com/clicklang/click/blob/master/mdtests/native_view_window.md)
for explicit proofs with `solve() using { ... }`.

Symbolic memory access usually needs:

- a covering viewed or owned memory resource, or a separate viewable range
- lower and upper index bounds
- loop invariants if the bounds are established by a loop

Viewed and owned memory resources imply viewability for the covered range. A separate
`viewable(...)` clause is useful when a proof needs viewability without access
permission, or when it needs a larger structural range than the immediate
permission covers.

A checked universal fact that reads every `int32` cell under the exact guard
`0 <= k and k < n` also certifies `viewable(p[0..n])` for that same memory and
base. This lets a modular copy or initialization postcondition re-establish the
initialized prefix without an extra ad-hoc viewability proposition. A narrower
guard, another base, or a read at another version point does not establish the range.

Use `viewable(p[lo..hi])` for the same kind of viewability fact when Click
expects a proposition, for example in a composite resource `fact`. `viewable`
does not grant read or write authority; it only supplies the pure fact needed
to justify loads from that range when the index bounds are known.

In an explicit proof, use proposition-level `at(...)` to refer to viewability
at a recorded point:

<!-- verified-example: mdtests/viewable_segment_forms.md -->
```click
have at(region(0).entry, viewable(p[0..n])) by {
    known();
}
```

This reads the whole viewability proposition at that point. In particular, its pointer,
range bounds, and memory state are all interpreted at `region(0).entry`.
Writing `viewable(at(region(0).entry, p)[0..n])` is not equivalent: that
would read only the pointer expression there but still ask whether it is viewable in
the current memory.

## Old memory

`old(expression)` evaluates in the function-entry state:

<!-- verified-example: mdtests/c_fragments_in_contracts.md -->
```click
ensures p[0] == old(p[0]);
```

For quantified old-memory postconditions:

<!-- verified-example: mdtests/forall_array_segment.md -->
```click
ensures segment_unchanged: forall (k: int32) {
    0 <= k and k < n implies p[k] == old(p[k])
};
```

Pointer-writing loops do not implicitly preserve old memory. Use explicit loop
invariants, loop effect summaries, or separation facts.

When an array parameter is passed to a pure Click function or predicate,
`old(p)` means the entry-state array ref, not just the old pointer value:

<!-- verified-example: mdtests/compare_swap2_permutation.md -->
```click
ensures pair_permutation: permutation::permutation(p, old(p), 0, 2) by {
    unfold(permutation::permutation);
}
```

The current `p` argument carries post-state memory. The `old(p)` argument
carries function-entry memory. Both carry the same C pointer value unless the
pointer variable itself changed.

Freeing an allocation ends its lifetime only in the current and later states. A load
inside `old(...)` remains a historical entry-state value when the entry
permissions and bounds justified that load; the corresponding current-state
load is still rejected as use-after-free.

## Write footprints and frames

Caller-owned ranges retained across a checked call use the shared address-class
owner selector. A transitive equality between native model pointers can select
a retained field even when the pointer spellings have different symbolic
blocks. Coverage still checks the complete byte extent; borrowed views do not
become owned frames, and a context without the alias has no lookup support.
Recorded call states can outlive the equality-input lineage that first
prepared their frame index. During recheck that index may identify a candidate
owner, but the current equality graph must establish the candidate's address;
the earlier graph supplies no equality evidence. This uses only the selected
owner, without republishing the frame or rechecking unrelated equality inputs.

A function's write footprint is the memory its contract owns:

<!-- verified-example: mdtests/contract_owns_write_footprint.md -->
```click
owns p[0..n];
owns dst[0..n];
owns counter[0..1];
```

A contract that owns nothing changes no memory visible at function entry.
Stack-local writes and initialization of a function-fresh allocation are always
allowed. The owned memory is an upper bound on externally visible writes, not a
promise that each cell changed. Allocation and deallocation must still satisfy
their separate allocation/resource obligations.

Static-storage objects are initialized once before program startup. The
designated program-entry state owns those initialized values; certifying an
ordinary function starts with the same storage objects but does not restore
initializers for mutable objects. A function may therefore rely on a mutable
initializer only through its precondition (for example, `requires counter ==
3`) or through the program-entry proof. Const-qualified objects are the
exception: because a valid C program cannot modify them, their initializers
remain stable facts. Calls preserve the caller's current static-storage
values.

Loop-level effects describe dynamic writes inside a loop. Step effects describe
one loop body iteration and may use iteration locals.

## Local stack memory

Local scalar address-of and local arrays allocate stack memory blocks named like
`local:x`. Local stack bookkeeping is not externally visible for function-level
effect checks.

Automatic storage is not initialized by declaration. A scalar declaration such
as `int32 x;`, a pointer declaration such as `int32* p;`, and the cells of a
local array have no readable value until the program writes them. Reading one
first is modeled as undefined behavior; taking its address or assigning to it
is allowed.

Example:

<!-- verified-example: mdtests/local_array.md -->
```c
int32 local_array_roundtrip() {
    int32 a[3];
    a[0] = 5;
    a[1] = 7;
    return a[1];
}
```

The local array block is ordinary memory for load/store semantics, but it does
not count as an external mutation.

A local's frame owns its bytes, so a function can lend a local array, or a
scalar's address, to a callee that owns its buffer, such as
`snprintf(tmp, sizeof(tmp), ...)`. Owning memory lets a callee write it but
does not say it did: a callee states the bytes it initialized with `ensures
defined(...)`, which its own proof checks, and after the call the caller may
read exactly those. The generated `snprintf` contract states `defined` for
each character it writes. Without such a postcondition a never-written cell
stays unreadable, even after a callee that owned it
(`mdtests/a_local_lent_to_an_owning_callee_is_initialized_after_the_call.md`,
`mdtests/a_local_no_callee_owned_is_still_uninitialized.md`).

## Click array refs

A pure Click function or predicate parameter written as an array or pointer:

<!-- verified-example: mdtests/click_array_refs.md -->
```click
predicate same_first(a: int32[], b: int32[]) {
    a[0] == b[0]
}
```

receives pure array refs for `a` and `b`. Each ref carries:

- a `Memory` value, the memory its reads are taken in
- a C pointer
- an element type, currently `int32` or `uint8`

Indexing `a[k]` inside the predicate loads from `a`'s carried memory, not from
some global ambient predicate memory. The element type decides pointer scaling
and whether the load yields an `int32` or `uint8` value. This lets
`same_first(p, old(p))`, or the standard `permutation::permutation(p, old(p), lo, hi)`,
compare post-state `p` to entry-state `p` without copying an array.

See [Surface Click and Kernel Click](surface-and-kernel.md) for the full C-pointer versus Click-array-ref
model.
