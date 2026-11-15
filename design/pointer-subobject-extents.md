# Pointer subobject extents: closing the scalar-subobject P1

Status: implemented; decisions D1-D5 and E1-E3 approved. This closes the
[scalar-subobject bug](https://github.com/clicklang/click/blob/8d8a621cc2fbbab3d9af29af22530fea8af8c26b/bugs/pointer-arithmetic-crosses-scalar-subobject.md) through the staged repairs below. It reuses
semantic conclusions from the archived object model (`design/cpp-object-model.md`
at `e3d84a785`) with a narrower representation.

## The hole, as it exists on master

Master `9ea01e78f` accepts every one of these (in the scratch reproductions, each
claim verifies):

| Variant | Source | Should be |
| --- | --- | --- |
| direct | `return *(&p->first + 1);` | reject the read |
| pointer local | `int32* q = &p->first; q = q + 1; return *q;` | reject the read |
| formation | `return &p->first + 2;` | reject the formation |
| modular helper | `arr(&p->first)` where `arr` has `views p[0..2]` and reads `p[1]` | reject the call |
| address equality, subobject | callee `if (q == p) return *q;` with only `views p[0..1]`; caller passes `&s->first + 1, &s->second` | reject the callee |
| address equality, whole objects | the same callee; caller passes `a + 4, b` with `views a[0..4]; views b[0..1]` | reject the callee |

The last row is not a subobject case: a one-past pointer of a separate array
reaches another object through a C-level address comparison inside a callee.
So the bug is two defects:

1. **Local (subobject extent).** The kernel never narrows a pointer to the
   member it was formed from. `&p->f` lowers to
   `AddressOf(TypedLoad{PointerOffsetBytes{p, off}, field_type})`. Formation
   (`pointer_offset_by_elements_paths`, `pointer_offset_by_bytes_paths` in
   `src/kernel/eval/operators.rs`) is checked only against held ranges
   (`held_range_membership`) or the whole block (`pointer_block_bounds`).
   Dereference (`read_c_lvalue_paths_without_ranges`, `write_c_lvalue_paths_*`)
   is checked only for address coverage by an owned or viewed range
   (`ResourceContext::permits_memory_read` / `memory_write_range`).
2. **Modular (designation across address equality).** In a callee, a pointer
   parameter is an opaque address. Authority lookup
   (`read_access_entries` through equality-graph pointer classes) accepts any
   pointer whose address is proven equal to a carrier that holds authority.
   That includes equality learned from a C `==`. In C, address equality
   does not make a one-past pointer dereferenceable.

## Principles

- **Extent is separate from authority.** Leave authority address-based and
  unchanged. Add one independent check: an access must stay inside the extent
  of the pointer that performs it. Address rewriting, aliasing and cell lookup
  never consult or alter extent.
- **Extent is carried in the value.** It is not reconstructed from addresses,
  held ranges or cell types.
- **Root extent stays as it is today.** The complete object or allocation is
  already enforced (block size, held ranges, `object_identity()`,
  `OnePastEndComparison`). The new mechanism adds only *narrowing* below the
  root.
- **No new contract syntax.** Existing resource clauses and spec equality carry
  the modular obligations (decisions D1 and D2).

## Phase A: subobject extents (local defect)

### Representation

Add `extent: PointerExtent` to `CPointerValue` (`src/kernel/primitives.rs:976`):

```rust
enum PointerExtent {
    /// No narrowing: the complete object or allocation, as enforced today.
    Root,
    /// A selected subobject in the same block, in byte offsets: [start, end).
    Subobject { start: PointerOffsetTerm, end: PointerOffsetTerm },
}
```

- Extent is part of value identity (`Eq`/`Hash`/`Ord` via `identity()`). Unlike
  `pointee_constant`, it is not ignored.
- Position is derived from the address; no separate position term is kept.
- `Root` is the default at all 35 `CPointerValue::new` sites, so landing the
  field alone changes no behavior.
- All 27 `into_pointer()` sites and 11 `replace_pointer` sites are audited.
  - A site that keeps using the value as a pointer must keep the extent.
  - Pure address uses (cells, aliasing, equality-graph keys) are correct
    to drop it.
  - The audit is a checked list in the PR.

### Producers

| Operation | Extent of result |
| --- | --- |
| Member selection `&p->f`, `&s.f` (C), member address (C++ `lower_place`/`CheckedObjectAddress`) | `Subobject[off, off + sizeof(f))` relative to the containing address. `f` may be a scalar, a nested record or an array member. |
| Array member decay `p->arr`, `&p->arr[i]` | the member array's extent (the whole `arr`, not the element) |
| Element of an array of records `items[i].y` | `y`'s extent within element `i` |
| Address of a declared object `&x`, array decay, `malloc`, string literal | `Root` (already exact: the block is the object) |
| Typed pointer arithmetic `q + n`, `q - n`, `&q[n]` | same extent as `q` |
| Copy, local assignment, argument binding, return | same extent |
| Store to memory, then reload of that exact cell | same extent: cached `CValue::Pointer` cells already return the stored value. The `pointer_read_stored_value` family in `memory_provenance.rs` must return the whole `CPointerValue`, not `Pointer`. |
| Reload of an unknown cell, havoc, modular result | Fresh opaque domain; formation and access require matching bounds evidence (Phase C) |
| Cast to a non-character object pointer type | same extent (a cast neither narrows nor widens; D3) |
| Cast between character-pointer types | same extent, including signedness changes (D4 refinement) |
| Cast from another pointer type to a character pointer, or any cast to `void*` | `Root` (byte view of the enclosing object; keeps `container_of`, D4) |

The frontend supplies each field's type and ABI size
(`CStructField::byte_width`). C member lowering records a `CExpression::Subobject`
at the selected address; C++ member and checked-object lowering use the same
kernel bounds rules. The Rust adapter currently refuses raw-pointer types;
its supported safe slice indexing checks `index < length` independently.

### Consumers

| Operation | Added check for `Subobject[s, e)` (none for `Root`) |
| --- | --- |
| Pointer formation (`pointer_offset_by_*_paths`) | `s <= result <= e` (one-past allowed) |
| Typed read or write of `w` bytes (`read_c_lvalue_paths_without_ranges`, `write_c_lvalue_paths_for_initialization`, `CheckedObjectAddress`) | `s <= addr` and `addr + w <= e` |
| Pointer subtraction / relational comparison | both operands have equal extents, in addition to today's same-object rule |
| C `==` / `!=` | unchanged (address comparison) |

Each check is two offset comparisons in the same block, decided by the existing
difference reasoning. That cost is constant per operation, independent of
unrelated state, as the
[efficiency contract](../docs/internals/verification-efficiency.md) requires.
A failure is reported as `pointer arithmetic left the pointed-to subobject` or
`read outside the pointed-to subobject`, naming the member's extent.

### Modular extent at calls (resource clauses as extent claims, D1)

At a call, each pointer argument with a `Subobject` extent must cover every
range that the callee's resource clauses name through that parameter.
`views p[0..2]` against `&s->first` requires `[p, p+8) ⊆ [first, first+4)`,
which fails, so the `caller` variant is rejected. Resource clauses already name
the carrier and range, so this needs no new syntax and only reads the clauses of
the selected callee. The callee assumes nothing new, so its proofs are unaffected.

The same check applies when folding a resource predicate whose body clause
names a `Subobject` pointer. This keeps
`fold(list(&s->node))` from claiming more than the member provides.

### What Phase A closes

direct, pointer local, formation, modular helper, and pointer-field store/reload
within one function (the extent travels with the stored `CValue`). It does not
close the two address-equality rows.

### Status after step 2

Delivered:
- `CExpression::Subobject { pointer, width }`, emitted by the C frontend for
  struct members and by C++ member-address lowering. Union members are not
  narrowed.
- Memory lvalues carry the extent, so `&*q` and `&q[i]` keep it.
- Formation and access are checked against the extent
  (`pointer arithmetic left the pointed-to object`,
  `access outside the subobject the pointer designates`).
- Loop abstraction keeps a pointer local's extent, and the back edge refuses
  a body that changes it.

Known limits, each refused or unchanged rather than accepted unsoundly:
- A loop that moves a pointer between different subobjects is refused at the
  back edge. Invariants cannot yet state which subobject a pointer
  designates.
- Pointers read from cells a call or loop havocs, and pointers loaded at
  function entry (including a static pointer's initial value), have no
  extent. A caller that formed such a pointer checks it against the callee's
  clauses at the call (step 3).
- A C pointer comparison still states pointer equality until Phase B.

### Status after step 3

A memory clause's range must lie inside the extent of the pointer that names
it, wherever the clause is evaluated: a call's requirements and results, a
composite body when it is expanded, folded or unfolded, and loop effect
clauses. The kernel checks it where a clause's base value becomes a range
(`segment_extent_refusal`); fold lowering refuses constant ranges by name
first. A pointer without an extent is unaffected.

A contract `==` between two pointers that both carry an extent also requires
the extents to be equal (D2), so a call cannot satisfy `requires q == p` with
`&pair->first + 1` and `&pair->second`. When either value has none, the
comparison stays an address equality: that value's designation may be
unknown, and assuming the equality must not refute a reachable path. A
contract's scalar member address `&p->f` is narrowed to the member as the C
frontend narrows it, so `ensures result == &p->second` does not hold for
`&p->first + 1`. Member loads and other contract spellings of member places
are not narrowed.

## Phase B: C `==` states address equality (modular defect)

Approved 2026-10-15. It replaces the earlier "designation is part of the
pointer value" plan, which is parked (see *Abandoned approach* below).

### Principle

C `==` on pointers compares addresses: `&pair.first + 1 == &pair.second`
holds, and only the second may be read through. So a C comparison should
tell the verifier exactly that, and no more:

- C `p == q` and `p != q` between object pointers state
  `address(p) == address(q)`, an equality of two `uint64` values. They do not
  state the kernel's pointer equality.
- Contract `==` between pointers keeps its meaning: the two are the same
  pointer value. `address(p) == address(q)` stays the spelling for an
  address-only claim.
- An address equality never becomes a pointer equality. Read and write
  permission follows pointer equalities, so `if (q == p) return *q;` cannot
  borrow `p`'s permission for `q`.

Equal things still behave the same way: equal addresses are equal integers,
and equal pointers are equal everywhere. Only the C comparison's claim is
narrowed to what C guarantees.

### What stays a pointer equality

Pointer equalities still come from value-level sources: contract `==`,
copies and pointer arithmetic over equal terms, a load and the value stored
in its cell, and resource argument binding. A comparison with the null
pointer constant is unchanged: C guarantees that a pointer equal to null is
null.

### Steps

1. Lower C pointer `==`/`!=` (except against null) to address equality, and
   stop deriving pointer equality from address equality.
2. Update the proofs that used a C comparison to conclude pointer equality.
   Each either states the address claim with `address(...)`, or relies on a
   value-level source. Add the two address-equality rows of the hole table as
   regressions.
3. Load congruence over address equality. Reads of one memory at equal
   addresses read one cell, so they are equal values; that grants no
   permission. Done: the equality graph keys every read by its state and
   numeric address (see `docs/internals/equality-closure.md`), and
   `mdtests/pointer_loads_equal_after_late_address_equality.md` passes again,
   with a displaced-field variant beside it.

Measured with steps 1 and 2 on master `979df5bbd`: three mdtests and one
example needed changes. `model_identity_pointer_payload`,
`loop_old_parameter_resource_argument` and `examples/modeled-binary-tree` now
compare addresses where their C does; the reads fixture waited on step 3.

### Abandoned approach

The earlier plan kept C `==` as pointer equality and added a separate
same-object condition, so that contract `==` meant "same address and same
object". It is parked on branch `claude/dreamy-darwin-2kvqba-same-object-wip`.
It needed the object to travel through every tactic, rewrite, load, loop and
memory transport, and it still left two mdtests and two examples failing on
reads of one cell across states. Narrowing the C comparison itself needs
none of that.

## Phase C: pointers of unseen formation

Status: implemented. Decisions E1-E3 were approved 2026-10-16. Phase B supplied
opaque complete-pointer identities uniformly for parameters, entry loads,
modular results, model payloads and havocked values. Phase C uses those identities
for formation and selection checks and reserves no separate producer variables;
the earlier unused `SubobjectExtent::opaque` prototype has been removed.

### What is checked

`extent == None` does not imply a complete object. `extent_is_known()` distinguishes
a declared object, allocation result or explicit widening cast from an unseen
pointer carrying `opaque_extent`. Executed arithmetic through the latter must
prove that the resulting position lies inside its own domain, including its
one-past endpoint. Zero displacement, including signed/native symbolic displacements proved
zero and subtraction of zero, preserves the original pointer. Selecting a member through an unseen
struct pointer also needs bounds for the complete selected member. A `T*` alone
does not supply `sizeof(T)` bytes.

Two complete programs already rejected by Phase B remain regression fixtures:
`a_loaded_member_pointer_keeps_its_subobject_in_a_callee.md` and
`an_incoming_one_past_pointer_keeps_its_subobject.md`. The remaining escape was
formation without a read: an unknown `p` could return `p + 2` using a wider
range named through an address alias, or no range at all. The new parameter,
loaded-pointer and modular-result fixtures reject that formation even with
`ensures true`. An uncovered member selection is rejected too.

### Bounds evidence

A typed memory clause establishes bounds for the pointer value that names it.
The held-range index supplies candidate ranges; complete domain identity admits
evidence. Numeric address equality selects addresses but never joins opaque
domains. Complete pointer equality can transfer bounds. A selected member keeps
its exact member extent, so a larger containing range cannot widen it.

Entry clauses, opened composites and unfolded instances retain coverage facts
under the existing `__click_subobject_covers_*` predicate. Facts are indexed by
the source pointer class and checked against its opaque domain. A nested clause
such as `views root->base.left` also retains the intermediate member coverage
established while its footprint was evaluated. `EvaluatedMemorySegment` and
`CMemoryRange::formation_coverage` carry that evidence to the producer that
publishes clause facts. Range identity and authority ignore this metadata;
rebasing and splitting retain it, and substitution maps its variables.

An owned allocation supplies bounds independently of byte ownership. Entry,
unfold and verified allocation-return producers publish its coverage, requiring
positive ownership. The token retains complete pointer identity: a member
pointer cannot claim an enclosing allocation token by address alone. This
permits taking a member address without making its bytes readable. Internal coverage facts are omitted from ordinary proof-context
lists; the source clauses and the actual refusal remain visible.

A position check does not require a readable element. The supplier's end is
included, and native 64-bit endpoints retain their width in coverage facts
and geometry checks. Those facts remain available after refolding memory. Checked nonnegative
32-bit endpoints can be promoted; native constants can be re-spelled narrowly
only when their complete byte footprint fits. Suffix windows retain the
non-wrapping subtraction evidence used by ordinary range containment. An empty
range cannot justify moving a pointer into it: either both operand and result
are the same contained position, or the supplying range must be nonempty.

Specification offsets remain mathematical address terms. Naming a footprint
is not executing C arithmetic; actual C formation and resource establishment
have their own checks. A resource clause's range still cannot claim beyond a
known selected member. C++ raw pointers use the common executed formation
checks, while reference binding retains its existing complete-referent storage
check. The Rust adapter rejects raw-pointer types (`rust/charon.rs`); safe slice
indexing keeps its own bounds checks and grants no raw-pointer arithmetic rule.

Rust slice entries publish formation coverage for the data pointer and native
length from the slice's inherent validity, including the `isize::MAX` byte-size
limit. This grants no readable bytes: metadata-only `split_at` proofs need no
view, while indexing still requires one. The frontend marks the adjacent length
argument, including across call/value-parameter splits; represented integer
lengths are observed numerically. Raw C pointer parameters carry no such mark.
Held resource bodies likewise retain their established bounds when projected
for call framing or for evaluating another resource clause's argument.

### Transport and cost

Unseen producers need no individual exemption: copies retain their domain,
complete equality relates domains, and havoc gets a fresh one. A loop's captured
entry view does not bound an independently reassigned cursor. The cursor fixture
now states and preserves its relation to the entry buffer without changing C.

Queries use the selected pointer-class coverage bucket and the held-range
interval index, with no walk over unrelated resources. Deterministic multi-size
regressions cover formation beside unrelated ranges and facts. Withdrawal tests
remove equality or coverage evidence and require the old bounds to disappear.
Fresh, expanded and retained checks cover full aliases, allocation-only bounds,
nested members and the moving cursor; a numeric-only alias is rejected again
in the retained session.

### Approved decisions

- **E1. Parameters need opaque bounds too.** Applied to every unseen producer.
- **E2. `T*` and `->` do not imply a complete `T`.** Selection uses stated bounds.
- **E3. Keep term-valued extent widths.** The existing term representation stays;
  Phase B's opaque domain identities select the coverage evidence used here.

## Decisions (approved as recommended)

- **D1. Resource clauses double as extent claims at calls and folds.**
  - Recommended: yes. There's no new syntax, and the meaning matches
    intent: `views p[0..2]` already says "p has two readable elements".
  - Alternative: a separate `valid(p[0..n])` clause. The archive's
    `valid_place` surface showed the migration cost.
- **D2. Spec `==` on pointers means value equality (address and extent).**
  - Recommended: yes. `address(p) == address(q)` remains for address-only
    claims.
  - Phase B keeps this meaning by narrowing the C comparison instead.
- **D3. Non-character casts keep extent but do not narrow.**
  - `((int32*)pair)[1]` on a `struct Pair*` stays accepted, because the
    struct's root extent covers both members.
  - Strict C makes `(int*)pair` designate `pair.first`.
  - Recommended: accept for now and track it as a follow-up. Narrowing on
    struct-to-first-member conversion is possible, but layout-dependent.
- **D4. Character and `void` casts widen to `Root`.**
  - This keeps the Linux `container_of` in `examples/rbtree/rbtree-augmented` and
    `mdtests/c_container_of.md` (`(void*)member - offsetof(...)`, then a cast to
    the enclosing type). It also keeps `memcpy` byte views
    (`examples/byte-representation`).
  - The consequence: `*(int32*)((char*)&p->first + 4)` is accepted. An explicit
    character round trip is the standard escape hatch, and compilers honor it.
  - On 2026-10-16 the user approved a refinement: casts between character-pointer
    types preserve the existing byte view, including across signedness changes.
    Compiler-inserted pointer conversions also preserve it. Explicit casts from
    other pointer types to characters, and every explicit cast to `void*`,
    still select the enclosing view. This preserves C-string borrowing and
    prevents character signedness changes from widening byte-member bounds.
  - Recommended: accept, and document it in `docs/`.
- **D5. Staging.**
  - Recommended: Phase A in three PRs:
    1. the carrier with `Root` everywhere, as a no-behavior-change audit;
    2. producers and consumers in C and C++, closing the local variants;
    3. the call/fold extent checks.
  - Phase B follows as its own PRs.
  - The bug file stays open, with the remaining rows updated, until Phase B
    lands.

## Validation

- Keep the original reproduction (direct) and every row above as mdtests,
  unchanged C:
  - negative fixtures for each rejected variant;
  - positive controls for `*(&p->first + 0)`, `&p->first + 1` formation without
    a dereference, `*(&p->second)`, member-array traversal, `container_of`,
    and `memcpy` byte views.
- Expected fixture churn: `a_loop_writing_past_a_sibling_field_forgets_the_union_view.md`
  (`p = &source.tag; p[2] = 9;`) changes from a refuted claim to a rejected
  store. Its C stays unchanged, and its expectation moves to the new refusal.
- Run all 52 example projects and the full mdtest corpus after each Phase A
  step. Any newly failing example is investigated, not adapted: either it
  relies on sibling traversal (a real finding to report) or the extent was lost
  in transport (a Phase A bug).
- Ordinary, expanded, rewritten and retained checking agree for the new
  fixtures (`click audit` on each).
- Scaling: a multi-size regression showing formation and access step work
  constant in the number of live subobject pointers.
