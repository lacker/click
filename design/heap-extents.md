# Heap-block extents: 64-bit (`size_t`) sizes

Status: option (a) accepted by the maintainer, 2026-11-10 (decisions D1-D6
below). The plan is complete: PR 0 (this note and a bug fix), PR 1 (the
tagged extent, stage 1), PR 2 (kernel 64-bit `malloc` and `free`, stage 2),
PR 3 (the sidecar and contract `uint64` byte count, stage 3) and PR 4
(`calloc` and `realloc`, stage 4) are done. Line numbers in section 1 are at `origin/master` e01ca8136
plus PR 0's changes (`statements.rs`, `primitives.rs`); stage 1 names its
sites by function.

This is the kernel prerequisite for `roadmap/standard-library.md` step 7,
"`size_t` sizes for `allocation`", and its intended regression ("an
`allocation` client whose byte count comes from a `size_t` expression, with no
narrowing to `int32`"). It finishes [typed-indices](typed-indices.md) stage 2
("The extent is `isize::MAX`") for heap blocks: stage 2 made contract ranges
wide (`RangeIndexKind::UInt64`, `src/kernel/primitives.rs:5589`) with the
extent fact `end <= i64::MAX / w` (`wide_memory_range_extent_guards`,
`src/kernel/primitives/contracts.rs:3250`), but left heap blocks 32-bit. Its
rulings apply: narrowing a 64-bit index into a 32-bit range is a dead end, a
64-bit index is never narrowed, and a range's kind does not depend on what a
contract happens to prove.

## 1. Current model

- **Token.** `abstract resource allocation(base: int32*, bytes: int32);`
  (`library/primitives.click:7`); the surface injects the same types
  (`src/surface/validation/declaration_expansion.rs:920-926`). In the kernel
  it is a `CResource::Token` with `[CValue::Pointer(base), CValue::Int32(bytes)]`:
  `own_allocation` / `own_designated_allocation`
  (`src/kernel/primitives/resource_algebra.rs:11544-11559`, wrapping bytes in
  `int32(..)`); `allocation_bounds_fact` (`:11562-11590`) and
  `allocation_value` (`:11593-11609`) match `CValue::Int32` only. The token
  carries lifetime and free authority, not access.
- **Access.** A separate owned range `p[0..count]`, built by
  `resolve_pending_heap_allocations` (`src/kernel/eval/statements.rs:2560-2705`)
  with `CMemoryRange::new_with_element_width`, so always
  `RangeIndexKind::Int32`. Its width is the pointee width when the byte count
  is `k*w` or a multiple of `w`, else bytes (`heap_range_element_width/_count`,
  `statements.rs:1501-1512`, via `element_count_from_bytes`,
  `src/kernel/reasoning/path_facts.rs:834-861`, which matches only an Int32
  `Multiply` or a 32-bit constant).
- **Heap state.** `CHeapMemory` (`src/kernel/primitives.rs:8508-8555`) maps
  pointers to untyped `MachineTerm` extents (live, deallocated, pending,
  zeroed-prefix); so do `CPendingReallocation.old_bytes` and `CBlock.size`
  (`primitives.rs:8688-8690`). The width is implicit; `memory_state.rs:4008`
  labels a reallocation's old bytes `CValue::Int32`.
- **Offsets** are already width-typed (`PointerOffsetTerm::Int32Scaled` /
  `Int64Scaled{unsigned}`, `primitives.rs:1018-1035`). `pointer_index_term`
  (`src/kernel/eval/operators.rs:2419-2446`) keeps a `size_t` index 64-bit and
  always zero-extends `uint32`. `pointer_block_bounds` (`operators.rs:2884-2990`)
  reads `CBlock.size` as unsigned 32 bits in its wide arms and as `int32` in
  its narrow arm.
- **malloc/calloc.** `execute_c_heap_allocate_paths` (`statements.rs:1288-1474`).
  The C front end lowers `calloc(n, w)` to `Multiply(n, w)` with
  `zeroed = true` (`src/languages/c/syntax.rs:14703-14826`).
  `heap_element_count_expression` (`statements.rs:1590-1607`) recognizes
  `e * w` / `w * e` syntactically and evaluates only `e`. `allocation_size_value`
  (`:1538-1588`) admits every value of 32 bits or narrower symbolically, and
  `Int64`/`UInt64` only when `exact_signed/unsigned_size_value` (`:1609-1685`)
  reduce it to a constant that fits `u32` (directly, through fact-proven
  equalities, or by `+ - *` of such constants). The element path decides
  positivity and `n <= i32::MAX / w` (`allocation_size_validity_refusal`,
  `:1687-1738`) and forms the Int32 `multiply(n, w)`; the raw path decides
  positivity, and for a `uint32` also `bytes <= INT32_MAX` (PR 0). The
  object-class check (`enough_space`, `:1414-1417`) is a 32-bit compare.
- **realloc** (`execute_c_realloc_assign_paths`, `statements.rs:1740-2253`)
  repeats the admission (`:1929-1979`); its prefix-preservation conditions are
  32-bit compares keyed on `AllocationSize.unsigned` (`:2119-2184`); a zeroed
  prefix must be constant (`:1981-2006`); `realloc(NULL, n)` reuses malloc.
- **free** (`execute_c_heap_free_paths`, `statements.rs:2255`) finds the token
  by base (`own_designated_allocation(pointer, 0)`, `:2308`), then consumes it
  and the full byte range `new_with_element_width(p, 0, bytes, 1)`
  (`:2403-2409`), independent of how the extent was spelled.
- **Contracts.** `allocation(result, e)` in a contract is evaluated at
  `src/kernel/functions.rs:19235-19300`, with its own `e * 4` shortcut that
  matches only the `int32` literal and a `CValue::Int32` count. `allocation`
  cannot be viewed (`declaration_expansion.rs:2846`); a symbolic quantity is
  refused (`functions.rs:18936`). Argument 0 accepts any data-pointer type
  (`src/surface/validation/type_validation.rs:3070-3090`); argument 1 has a
  64-bit refusal hint (`:3055-3066`).
- **Ranges** of `Int32` kind are capped at a `u32` byte count
  (`memory_range_element_count_limit`, `contracts.rs:2830`;
  `memory_range_byte_count_extent`, `:2905`); wide ones at `i64::MAX / w`. The
  ordered interval index uses signed-32 coordinates
  (`resource_algebra.rs:145`, `:1150-1182`), and `concrete_memory_range_bounds`
  gives up on wide ranges (`contracts.rs:2433-2439`): wide ranges are never
  interval-indexed.
- **Diagnostic.** `CRuntimeError::HeapAllocationSize` (`primitives.rs:7419`,
  message `:7760`; `HeapAllocationSizeAboveInt32` beside them;
  `src/surface/diagnostics.rs:1662`;
  `src/kernel/api/contract_certification.rs:841`).
- **Docs.** `docs/reference/language/c.md:2154-2159, 2606-2650, 2675-2681`,
  `docs/reference/language/index.md:2820` ("checked 32-bit extent").

Why 32-bit: the heap model predates typed indices, when every range was
`Int32`; stage 2 widened contract ranges and left the heap constructor alone
(comment at `statements.rs:1532-1537`). 085788448 (2026-11-07) added
`HeapAllocationSize`.

### Sites a 64-bit extent touches

| Site | 32-bit today |
|---|---|
| `library/primitives.click:7`, `declaration_expansion.rs:926` | `bytes: int32` |
| `type_validation.rs:3055-3066` | 64-bit refusal hint |
| `resource_algebra.rs:11544-11609` | token built and matched as `CValue::Int32` |
| `resource_algebra.rs:11623-11660`, `path_facts.rs:834-861` | separation via `element_count_from_bytes` (Int32 only) |
| `statements.rs:1372-1417` | `multiply(n, w)` Int32; `enough_space` |
| `statements.rs:1501-1738` | element width/count, size admission, positivity/fit |
| `statements.rs:1929-2006, 2119-2184` | realloc admission and fit compares |
| `statements.rs:2308, 2403-2409, 2560-2705` | free's range and token; pending resolution |
| `primitives.rs:8508-8555, 8688-8690`; `memory_state.rs:3582-3587, 3946-3980, 4008` | untyped extents, implicit 32-bit reading |
| `operators.rs:2884-2990` | `pointer_block_bounds` |
| `functions.rs:19235-19300` | contract `allocation(p, e*4)` |
| `resource_algebra.rs:145, 1177-1182` | interval-index coordinates (not heap-specific) |

### Corpus

No integration (bitcoin money range, linux rbtree, libcxx fixtures) allocates
on the heap; C++ `new` and Rust `Box` lower to a constant
`c_int32_literal(size)`. Constant sizes (`sizeof(T)`, `k * sizeof(T)`,
literals) dominate; they are 64-bit constants the exact-constant path admits.
About 15 call sites use a symbolic `int32` count with an explicit
`count <= INT_MAX / w` requirement. The only `size_t` clients
(`mdtests/integer_heap_widths.md`) pin `count == 2/3`. No fixture allocates a
bounded symbolic `size_t`, although `malloc(n * sizeof *p)`, `malloc(len + 1)`
and `calloc(n, sizeof(T))` with `size_t n` are the idiomatic forms. All 127
`allocation(` sidecars use `int32` or constant byte counts; extern allocators
with a `size_t` extent write `bytes as int32`
(`an_extern_allocator_states_a_bounded_64_bit_extent_as_int32.md`).

### Probes (2026-11-10, debug binary at 17fb0ad3c)

- Refused with `HeapAllocationSize`, all with bounded `size_t` sizes:
  `malloc(n * sizeof(uint32_t))` (`1 <= n <= 100`); `calloc(n, sizeof(uint16_t))`
  (shown as `calloc((n * 2u64))`); `realloc(data, n * sizeof(uint64_t))`;
  the overflow-safe cast `malloc((size_t)count * sizeof(uint32_t))` with
  `int count`; `malloc(len + 1)` with `len <= 4096`.
- Extern allocator `produces allocation(result, bytes);` with `size_t bytes`:
  type error, "resource `allocation` argument 1 expects int32, got uint64".
- Control: `int n`, `malloc(n * sizeof(uint32_t))`, store, read, free: passes.
- A wide parameter range (`owns bytes[0..length]`, `uint64 length`) already
  accepts an `int32` index: passes.
- `produces allocation(result, bytes as int32); produces result[0..bytes];`
  (wide range beside an `int32` token), then `data[n - 1]` with a `size_t`
  index and `free`: passes; free's Int32 full-range request is met by the wide
  range. One byte short: free refused with `missing resource fact owns
  ((char *)data)[0..(n as uint32)]`. Cross-kind consumption is checked.
- `abstract resource sized(p: int32*, k: Integer);`: "algebraic resource
  arguments are not supported yet" (blocks option (c)).
- `uint32` size `>= 2^31` (`malloc(n)` with `n == 3000000000u32`): accepted,
  then `p[0]` refused as "pointer arithmetic left the pointed-to object"; the
  resources showed `allocation(p, int32(n))` and `p[Int32:0..n]`. Fixed in PR 0.

## 2. Constraints every option respects

- `size_t` arithmetic wraps without UB: `malloc(n * w)` allocates
  `(n*w) mod 2^64`, a real block. Reading `e*w` as an exact product needs a
  decided no-wrap condition; otherwise the C product itself is evaluated.
- `calloc(n, w)` returns null when `n*w` is not representable (C17 7.22.3.2,
  explicit in C23). Click lowers it to `Multiply(n, w)`, safe only while the
  kernel never evaluates that as a wrapping product.
- An object above `PTRDIFF_MAX` bytes makes pointer subtraction within it
  undefined (C17 6.5.6p9). Click's wide-range extent is `end <= i64::MAX / w`,
  so a 64-bit block's ceiling is `PTRDIFF_MAX` bytes, proved at the allocation
  (not assumed at entry, as contracts are).

## 3. Options

- **(a) Accepted. A tagged extent `HeapExtent { term, kind: Int32 | UInt64 }`.**
  The kind comes from the size's C type. Every 32-bit and narrower value and
  every term-constant 64-bit value that fits stays `Int32`; a symbolic
  `Int64`/`UInt64` value is `UInt64` (a signed one read as its sign extension,
  so a negative one fails the extent guard). The `UInt64` block's token holds
  `CValue::UInt64`, its range is `new_wide`, and accesses use the existing
  `Int64Scaled` offsets and wide membership, as wide parameter ranges do.
  Constant-size blocks stay `Int32` and interval-indexed.
- (b) Rejected (D6): keep 32-bit and narrow a bounded `size_t` under
  `E <= i32::MAX`. Smallest change, but it is the narrowing typed-indices
  ruled out, caps blocks at 2 GiB, makes acceptance fact-dependent, and needs
  the `n as int32` round-trip rule.
- (c) Deferred: an `Integer` extent. Needs Integer resource arguments
  (refused today), still needs a machine range kind, and moves Integer
  reasoning into resource-argument equality on the hot path.
- (d) Rejected (D1): one uniform `UInt64` heap kind. Moves every constant-size
  block out of the interval index and changes every heap token spelling.
- (e) Rejected (D3): a trusted allocator-limit model (null above
  `PTRDIFF_MAX`).

## 4. Decisions (maintainer, 2026-11-10)

- **D1.** Extent width by the size's C type, as in (a).
- **D2.** A `size_t` size the facts fix to a constant (`requires count == 2`,
  `integer_heap_widths.md`) stays a 32-bit constant extent, as today.
- **D3.** An unbounded `size_t` size must be proved `bytes <= PTRDIFF_MAX` at
  the allocation; there is no trusted "returns null" assumption.
- **D4.** `allocation`'s byte count stays declared `int32` and also accepts
  `uint64`, mirroring argument 0's pointer-type independence.
- **D5.** A 32-bit size spelled against a 64-bit block's `allocation` resource
  is refused with a message naming the kinds; no cross-kind argument equality.
- **D6.** No 32-bit narrowing stopgap ((b) does not ship). The
  extern-allocator `bytes as int32` form stays legal and means what it says.

A `uint32` size stays `Int32` under D1, so one above `INT32_MAX` stays refused
after PR 2; accepting it would need a separate decision to give `uint32` sizes
the `UInt64` kind.

## 5. Staged plan

0. **Landed: bug fix and this note.** `allocation_size_value` admitted a
   `uint32` size as unsigned, deciding only positivity or `n <= u32::MAX / w`,
   and stored it in the `int32` token and Int32 range, where `>= 2^31` read
   negative. A `uint32` size (`AllocationSize.needs_extent_bound`) must now be
   decided at most `INT32_MAX` bytes (raw) or `INT32_MAX / w` elements, for
   `malloc`, `calloc` and `realloc`; otherwise the allocation is refused with
   `CRuntimeError::HeapAllocationSizeAboveInt32`. Regressions:
   `mdtests/a_uint32_malloc_size_above_int32_max_is_refused_at_the_malloc.md`,
   `a_uint32_element_count_above_the_int32_heap_extent_is_refused.md`,
   `a_uint32_realloc_size_above_int32_max_is_refused_at_the_realloc.md`,
   `a_uint32_malloc_size_bounded_by_int32_max_allocates.md`.
1. **Done: tagged extent, no behavior change.** `HeapExtent { bytes, kind }`
   with `HeapExtentKind::{Int32, UInt64}` (`src/kernel/primitives.rs`). It is
   the value of `CHeapMemory`'s live, deallocated and pending maps,
   `CPendingReallocation.old_bytes` and `CBlock`'s size
   (`CBlock::extent`, `CMemory::block_extent`, `live_heap_block_extent`);
   `AllocationSize` carries `kind`. Every extent is `Int32`. An `Int32` extent
   hashes and prints as its byte term, so state hashes, load names and
   traces are unchanged; equality and ordering compare the kind after the
   bytes. Threaded through the kind: the token
   (`own_heap_allocation`/`own_designated_allocation` build `int32` or
   `uint64` from the extent; `allocation_extent` reads it back;
   `allocation_value` and `allocation_bounds_fact` accept both); the owned
   and byte ranges of malloc resolution, realloc resolution, realloc and free
   (`HeapExtent::range`/`byte_range`, `heap_block_range` in `statements.rs`:
   `new_wide` for `UInt64`); `AllocationSize::scaled` (the `uint64`
   product); `enough_space` (`HeapExtent::unsigned_less_equal`); the
   separation of a retired allocation (`is_proven_separate_from_allocation*`,
   `caller_resource_left_stale_by_retirement`, `refuse_retiring_a_lent_allocation`,
   `lent_owned_memory_covers_allocation`); contract claims take the kind
   from the token; `pointer_block_bounds` reads the size through the tag
   (`uint64_bytes`/`int64_bytes` in the 64-bit arms, `int32_bytes` in the
   32-bit ones); `ReadRegionIdentity` compares extents. Refused for a
   `UInt64` extent until a later stage reads it: `allocation_size_validity_refusal`
   (`HeapAllocationSize`), realloc of a `UInt64` block or to a `UInt64` size
   (stage 4), the 32-bit arms of `pointer_block_bounds` (no normal path),
   `pointer_at_block_end_condition` (may be the end) and
   `proves_loadable_cell_from_region` (not loadable). Kernel unit tests:
   `src/kernel/primitives/heap_extent_tests.rs`. No new scaling test: no
   operation does more work per step (one tag byte per extent, the same
   hashing, no new scan or index).

   What stage 2 now changes. Allocation sites: `allocation_size_value` gives
   a symbolic `Int64`/`UInt64` size `kind: UInt64`, and
   `allocation_size_validity_refusal` replaces its `UInt64` refusal with the
   size proof below (and keeps calloc refused until stage 4). Two readers:
   the 32-bit arms of `pointer_block_bounds` compare a widened 32-bit offset
   with the 64-bit extent instead of refusing (a wide parameter range accepts
   an `int32` index), and `heap_range_element_count` (the typed width of the
   wide range) and `is_proven_separate_from_allocation*` need the `uint64`
   element count (`n * w` at `uint64`, a `uint64` constant). Caution for the
   plan's "`element_count_from_bytes` gains a `UInt64` arm": its twenty other
   callers build 32-bit ranges from its result, so an arm added in place
   hands them a `uint64` count; a kind-aware entry point avoids that (open
   for stage 2 to settle). Still term-only and conservative for a `UInt64`
   block while that holds (each gives up rather than misreads): the `bytes` of
   `CMemoryDerivation::{HeapAllocated, HeapAllocationPending, HeapFreed,
   ContractAllocationRetired}` (`heap_allocation_proven_separate_from_pointer`
   reads them as 32-bit), `Proposition::CHeapAllocationFreed.bytes` with
   `heap_free_effect_is_valid` (reinstates a 32-bit claim), and zeroed
   prefixes (constant only). `allocation_continuity` compares byte terms at
   `int32`; stage 3 makes it refuse a cross-kind pair (D5). Free's token
   lookup indexes by name, arity and base, so it already finds a `uint64`
   token.
2. **Done: kernel 64-bit malloc and free, with the size proof.**
   `allocation_size_value` gives a symbolic `Int64`/`UInt64` size
   `kind: UInt64` (a `long` as its `size_t` conversion, so a negative one
   fails the guard); a 64-bit size the facts fix to a constant stays a
   32-bit constant when it fits `uint32` (D2) and is a `uint64` constant
   otherwise. `allocation_size_validity_refusal` decides, through
   `uint64_allocation_size_is_exact`: element path `1 <= n <= i64::MAX / w`,
   then the exact `uint64 n * w`; raw path `1 <= E <= i64::MAX`, and when
   `E` is itself a top-level `uint64` product with a constant `k`,
   `1 <= other <= i64::MAX / k` instead (a product of two symbolic factors
   is refused). That last rule is what makes the kind-aware reader sound: a
   `size_t` product may wrap without undefined behavior, and its wrapped
   value at most `PTRDIFF_MAX` says nothing about its factor, so a reader
   may take `n * k` bytes as `n` elements only because every admitted
   `uint64` product extent has its factor bound decided. Wrapped products:
   when the element guard is undecided for a `size_t` count, the size is
   C's `size_t` product `uint64 n * w`, evaluated through the same constant
   folding (D2) and admitted as a raw size. A count the facts fix gives the
   wrapped constant (`n == 2^62 + 1`, `malloc(n * 4)` is 4 bytes); a
   symbolic one is a top-level product whose factor bound already failed,
   so it is refused. A `long` count is never wrapped (`long * int` may
   overflow). calloc and `realloc` to or of a `UInt64` size stay refused
   (stage 4); calloc never forms its product. `realloc(NULL, n)` is
   `malloc(n)` and admits one.
   Readers: `element_count_from_bytes` is unchanged; the kind-aware entry
   point is `HeapExtent::element_count` (`uint64_element_count_from_bytes`
   for a `UInt64` extent: `n` of `uint64 n * w`, or a divisible `uint64`
   constant), used by the heap range of malloc, free and pending resolution
   (`heap_range_element_count`) and by `is_proven_separate_from_allocation*`.
   `pointer_block_bounds`: a 64-bit offset into a `UInt64` block compares
   with its element count where the extent spells one; a 32-bit offset
   (`wide_block_bounds_of_32_bit_offset`) compares a sign-extended scaled
   `int32` index with that count at `int64`, any other exact offset with
   the byte count, and an offset with no exact reading has no normal path.
   Left conservative for a `UInt64` block (each gives up rather than
   misreads): `pointer_at_block_end_condition` (may be the end),
   `proves_access_from_memory_block` (not loadable from the block alone;
   access comes from the owned range), the derivation and
   `CHeapAllocationFreed` byte terms (a free in the allocating function
   matches the live extent; reinstating a claimed `UInt64` block's extent is
   stage 3), zeroed prefixes. Diagnostic: `HeapAllocationSize` now reads
   "heap allocation size must be proved to fit a heap block" and names the
   `PTRDIFF_MAX` bounds. A 64-bit block cannot cross a call until stage 3
   (a sidecar cannot spell its token). Regressions (mdtests):
   `a_bounded_size_t_element_count_allocates_a_64_bit_block`,
   `a_size_t_byte_count_plus_one_allocates_a_64_bit_block`,
   `an_int_count_cast_to_size_t_allocates_a_64_bit_block`,
   `a_size_t_product_byte_count_allocates_its_elements`,
   `an_int_and_a_size_t_index_address_a_64_bit_block`,
   `a_loop_writes_every_element_of_a_64_bit_block`,
   `an_unbounded_size_t_malloc_size_is_refused` (replaces
   `a_symbolic_64_bit_malloc_size_names_the_32_bit_heap_extent.md`),
   `a_size_t_element_count_whose_product_may_wrap_is_refused`,
   `a_wrapping_size_t_product_allocates_only_the_wrapped_bytes`,
   `a_product_of_two_symbolic_size_t_sizes_is_refused`,
   `a_store_past_a_64_bit_block_is_refused`,
   `a_64_bit_block_freed_twice_is_refused`,
   `an_interior_free_of_a_64_bit_block_is_refused`,
   `a_store_into_a_freed_64_bit_block_is_refused`,
   `a_symbolic_size_t_calloc_count_is_refused` and
   `a_realloc_of_a_64_bit_block_is_refused` (both replaced in stage 4).
   Kernel unit tests
   (`heap_tests.rs`: the token, extent and wide range after resolution; the
   refusals; the wrapped block; `heap_extent_tests.rs`: the element count).
   Scaling (`memory_scaling_tests.rs`):
   `one_store_into_a_64_bit_heap_block_is_logarithmic_in_unrelated_64_bit_allocations`
   (pointer formation against the 64-bit extent and the store, beside N
   wide-owned 64-bit blocks) and
   `normalizing_64_bit_allocation_tokens_in_distinct_heap_blocks_is_linear`.
   The surface `stores_beside_many_owned_ranges` and `allocation_continuity`
   copies need a 64-bit block to cross a call, so they move to stage 3.
3. **Done: sidecar and contract 64-bit byte count, and docs.** `allocation`
   argument 1 stays declared `int32` (`primitives.click`,
   `declaration_expansion.rs`) and also accepts `uint64` (D4):
   `resource_types_compatible` in `type_validation.rs` (its type message now
   names both formats, and refuses a signed 64-bit count),
   `c_value_matches_allocation_extent` in surface lowering, and the kernel's
   argument type check in `evaluate_function_declared_resource_spec`
   (`functions.rs`). There a `uint64` count goes through
   `uint64_allocation_extent_argument`: a constant in `1..=INT32_MAX` is the
   32-bit extent (`16u64` is `16`, as `malloc` makes it, D2); any other value
   is a 64-bit extent only under `malloc`'s decision, now shared as
   `uint64_heap_extent_bytes_are_exact` (`eval/statements.rs`):
   `1 <= E <= PTRDIFF_MAX`, and for a top-level product with a constant `k`,
   `1 <= n <= PTRDIFF_MAX / k`; a product of two symbolic factors is refused.
   The ordinary evaluator gives `n * 4u64` the same `uint64` product term as
   `AllocationSize::scaled`, so no `e * 4` shortcut is needed. The decision
   is made wherever a token is formed (a requirement at a call, a clause
   produced at an exit, a clause an opaque or `extern` call returns to its
   caller) and assumed where the clause was established elsewhere: a
   contract's own entry clauses and a held body
   (`assume_entry_clause_extents`). Soundness: every `uint64` token in a
   context was formed under the decision, by `malloc` or by such an
   evaluation, so `uint64_element_count_from_bytes` still reads only exact
   products; an entry clause is established by every caller, which decides
   the clause instantiated with its arguments, so a caller cannot pass
   `allocation(p, k * 4u64)` for a `k` whose product wrapped onto its own
   block's extent.
   D5: `allocation_extent_kind_refusal` (`functions.rs`), on a call's
   missing `allocation` requirement, finds the caller's token at the same
   base by the context's argument index and, when its format differs,
   refuses naming both formats. `allocation_continuity` takes the two
   `HeapExtent`s and compares same-format extents in their format
   (`c_values_proven_equal_for_memory_resolution`, `uint64` equality for two
   64-bit ones); a cross-format pair at bases not proven distinct is
   `AllocationContinuity::CrossKind`, refused at the call.
   Readers left conservative by stage 2 that a crossing block reaches:
   `Proposition::CHeapAllocationFreed.bytes` is now a `HeapExtent`, so
   `heap_free_effect_is_valid` reinstates a claimed block's extent in its own
   format, the region footprint of a free uses the extent's byte range (it
   built an `Int32` range from a `uint64` term), the join guard of
   conditional frees (`interface_resources_guard_heap_frees`) compares
   extents, and `heap_allocation_proven_separate_from_pointer` reads the
   extent's element count in its kind. The `CMemoryDerivation` byte terms
   stay untyped and are read as 32-bit there (a 64-bit block's term spells
   no 32-bit element count, so the separation is not proved), as are
   `pointer_at_block_end_condition`, `proves_access_from_memory_block` and
   zeroed prefixes. Regressions (mdtests):
   `an_extern_allocator_states_a_size_t_extent` (replaces
   `an_extern_allocator_with_a_64_bit_extent_names_the_32_bit_heap_extent.md`),
   `an_extern_size_t_extent_whose_product_may_wrap_is_refused`,
   `a_callee_frees_a_64_bit_block_it_consumes`,
   `a_store_after_a_callee_frees_a_64_bit_block_is_refused`,
   `a_64_bit_allocation_requirement_is_assumed_at_entry`,
   `a_call_naming_a_64_bit_extent_with_an_unbounded_count_is_refused`,
   `a_callee_keeps_a_64_bit_block_its_caller_frees`,
   `a_function_returns_a_bounded_64_bit_malloc_block` (the case the removed
   `a_symbolic_64_bit_malloc_size_names_the_32_bit_heap_extent.md` covered),
   `a_32_bit_allocation_spelling_of_a_64_bit_block_is_refused`,
   `a_64_bit_allocation_spelling_of_a_32_bit_block_is_refused`,
   `a_returned_allocation_of_the_other_extent_format_is_refused`,
   `a_signed_64_bit_allocation_byte_count_is_refused`;
   `an_extern_allocator_states_a_bounded_64_bit_extent_as_int32.md`
   unchanged (D6). Kernel unit tests: the contract extent decision and
   cross-format continuity (`functions/allocation_continuity_tests.rs`), a
   free effect's 64-bit reinstatement (`heap_free_effect_tests` in
   `contract_claims.rs`). Scaling: the kernel
   `uint64_allocation_size_graph_queries_scale_without_fact_index`, and the
   surface `stores_beside_many_owned_64_bit_blocks_scale_near_linearly` and
   `calls_borrowing_a_64_bit_block_scale_near_linearly` (nightly). Closes the
   step 7 item and its intended regression. Not changed: a `size_t` count the
   facts fix to a constant still makes a 32-bit block (D2), so a contract
   states its token with the constant (`allocation(p, 8)`), not with
   `n * 4u64`, which is of the other format and refused (D5).
4. **Done: calloc and realloc.** calloc never evaluates its product:
   `execute_c_heap_allocate_paths` splits the lowered `n * w` into its count
   and constant element size (`calloc_operands`; `w` may be a struct size
   other than the target's element width) and evaluates only `n`. The count
   takes the element path with width `w`: a 64-bit count must be decided
   `1 <= n <= PTRDIFF_MAX / w` (`uint64_allocation_size_is_exact`), then the
   extent is the exact `uint64 n * w`; an undecided guard is refused with
   `HeapAllocationSize`, with no wrapped-product fallback (that is
   `malloc`'s), so a count the facts fix where the product wraps is refused
   rather than modeled as the wrapped block, as the base did for a struct
   `calloc`. A 64-bit `calloc` size not of that shape (no front end makes
   one) is refused. The zeroed reading needs no change: it is per block.
   Because only the count is evaluated, a struct `calloc` with an `int`
   count is now a 32-bit block (`n * w` at `int32`, `n <= INT32_MAX / w`
   decided), where the evaluated `size_t` product made it a refused 64-bit
   size before; the C reference already documented that form
   (`a_struct_calloc_with_an_int_count_allocates_a_32_bit_block`).
   realloc: the `Int32`-only filters are gone. The new size is admitted as
   `malloc`'s (element path `1 <= n <= PTRDIFF_MAX / w`, raw path
   `uint64_heap_extent_bytes_are_exact`), without the wrapped-product
   fallback. The old block's token, complete range, byte range and the
   separation of its dependents were already kind-aware (stages 1-3), as are
   pending resolution and free. The fit conditions for copied cells and
   initialized runs are `AllocationSize::at_least` / `less_than`: the old
   32-bit compares for an `Int32` size, and for a `UInt64` one
   `uint64_extent_in_elements`, which compares `ceil(end / k) <= n` for an
   extent `n * k` with a constant `k`. That is exact because such an extent
   was admitted with `n <= PTRDIFF_MAX / k` decided, and it is what the facts
   about `n` decide where the wrapping product would not. A constant zeroed
   prefix stays the supported case, now computed by
   `realloc_zeroed_prefix`: the minimum of two constants, or the one constant
   (old prefix or new size) the facts decide is the smaller, compared in its
   own format. A prefix that would not be a constant (a 64-bit `calloc`
   block grown to another symbolic size) is refused as before. The same rule
   admits a 32-bit symbolic size from a constant zeroed source where the
   facts decide the order, refused before
   (`a_zeroed_block_reallocated_to_an_int_size_keeps_its_zeroed_prefix`). The diagnostic names `calloc(n, w)` and
   `realloc(p, n * w)`. Regressions (mdtests):
   `a_bounded_size_t_calloc_count_allocates_a_zeroed_64_bit_block`,
   `a_size_t_calloc_count_with_no_upper_bound_is_refused` (replaces
   `a_symbolic_size_t_calloc_count_is_refused`),
   `a_calloc_count_whose_product_would_wrap_is_refused`,
   `a_realloc_grows_a_64_bit_block_and_keeps_its_prefix` (replaces
   `a_realloc_of_a_64_bit_block_is_refused`),
   `a_realloc_shrinks_a_64_bit_block_and_keeps_its_prefix`,
   `a_realloc_of_a_32_bit_block_to_a_size_t_size_keeps_its_prefix`,
   `a_zeroed_block_reallocated_to_a_size_t_size_keeps_its_zeroed_prefix`,
   `a_zeroed_64_bit_block_reallocated_to_a_constant_size_stays_zeroed`,
   `a_size_t_realloc_size_with_no_upper_bound_is_refused`,
   `a_store_past_a_reallocated_64_bit_block_is_refused`,
   `a_store_through_the_old_pointer_after_a_64_bit_realloc_is_refused`,
   `a_64_bit_block_freed_after_its_realloc_is_refused`. Kernel unit tests
   (`heap_tests.rs`): a zeroed 64-bit calloc block, the calloc refusals
   (fixed wrapping count, unbounded count), and a 64-bit realloc's consumed
   and produced tokens and ranges. No new scaling test: no hot path changed
   (each realloc fit condition is one decision per cached cell or
   initialized run, as before, and the element reading is a constant-size
   term match).

   Still conservative after stage 4, each giving up rather than misreading:
   a nested product such as `realloc(p, n * 2 * w)` (its count `n * 2` is a
   wrapping product whose bound the facts do not decide; `malloc` refuses it
   too), and the `CMemoryDerivation` byte terms,
   `pointer_at_block_end_condition` and `proves_access_from_memory_block`
   listed under stages 2 and 3.

   **Done after stage 4: fields of a 64-bit struct-array block.** `malloc`
   or `calloc` of `n * sizeof(struct T)` with a `size_t` or `int` `n` (an
   `int` count times `sizeof` is a `size_t` product) makes a block of
   `n * k` bytes owned as the wide byte range `p[0u64..n * k]`, and
   `p[i].field` is the byte address `p + (int64)i * k + c`. Both readers
   compared that byte offset with the wrapping product `n * k`, which the
   facts about `n` do not decide, so a field access was refused as leaving
   the object. They now compare in elements, the reading
   `uint64_extent_in_elements` and `HeapExtent::element_count` already make
   (`scaled_element_offset` and `wide_index_bound_conditions`,
   `reasoning/path_facts.rs`): a constant offset `c` is
   `ceil(c / k) <= n`, and `i * k + c` with `0 <= c < k` is `0 <= i <= n`
   for the address when `c == 0`, else `0 <= i < n`, and `0 <= i < n` for
   an access of at most `k - c` bytes. A signed index whose `uint64`
   reading the facts decide is compared unsigned: for `n <= PTRDIFF_MAX`,
   `0 <= i <= n` signed iff `i <= n` unsigned, and a `size_t` index
   converted to `ptrdiff_t` keeps only `uint64` facts. Formation
   (`wide_element_block_bounds`, `eval/operators.rs`) relies on the
   admission decision `n <= PTRDIFF_MAX / k` of the block's extent, as
   `element_count` does; membership in a wide byte range whose end is a
   product `m * k` (`field_access_in_wide_struct_array`,
   `assumptions/memory_reasoning.rs`) decides `m <= PTRDIFF_MAX / k` itself,
   since a range need not end at an admitted extent. Under those bounds
   `n * k` and `i * k` are the mathematical values, so each element
   comparison is equivalent to the byte one; the rule only adds accepted
   accesses, and the whole-element rule stays the fallback. Regressions
   (mdtests): `a_size_t_struct_array_malloc_block_writes_and_reads_its_fields`,
   `an_int_count_struct_array_malloc_block_writes_and_reads_its_fields`,
   `a_size_t_struct_array_calloc_block_writes_and_reads_its_fields`,
   `a_size_t_struct_array_calloc_block_reads_zero_fields`,
   `a_size_t_struct_array_block_is_accessed_after_a_call_taking_its_allocation`,
   `a_field_past_a_size_t_struct_array_block_is_refused`,
   `a_first_field_one_past_a_size_t_struct_array_block_is_refused`,
   `a_field_at_an_unbounded_index_of_a_size_t_struct_array_block_is_refused`.
   Kernel unit test
   `a_field_access_in_a_wide_struct_array_byte_range_is_placed_over_elements`
   (`tests/resource_tests.rs`); scaling
   `one_field_store_into_a_64_bit_struct_array_block_is_logarithmic_in_unrelated_blocks`
   (`memory_scaling_tests.rs`).

   **Done after stage 4: struct ranges of a 64-bit block.** A contract's
   `owns p[0..n]` on a struct pointer with a `size_t` `n` is the wide range
   `p[0u64..n]` of `k`-byte elements, and the block is the byte range
   `p[0u64..n * k]`. Coverage and subtraction
   (`memory_range_covers_by_routes`, `split_memory_range` in
   `primitives/resource_algebra.rs`) now re-spell a wide range in the other
   range's element width (`wide_memory_range_respelled`): narrowing the width
   multiplies each symbolic endpoint by `m = from / to`, widening it reads an
   endpoint `x * m` (a `uint64` product with the constant `m`) as `x`, and
   constants are folded exactly. Each product carries its no-wrap condition
   `x <= UINT64_MAX / m`, decided (one decision per symbolic endpoint) before
   the re-spelling stands for the range: then both spellings name the same
   bytes, so no byte is added or dropped. The requirement is re-spelled in
   the owner's width first, keeping residues in the owner's coordinates, then
   the owner in the requirement's. A block's count was admitted with
   `n <= PTRDIFF_MAX / k` decided and a contract's struct range carries its
   extent guard `n <= PTRDIFF_MAX / k`, so the condition is decided for
   every block a caller allocated; it is open only for a byte range a
   contract states over an unbounded count. That gives a call's or loop's
   entry the struct range, and its exit, a `free` or a later call the byte
   range back. Field access through a held struct range reuses the
   struct-array rule over the range's own count
   (`wide_struct_array_count` and `field_access_in_wide_struct_array`,
   `assumptions/memory_reasoning.rs`, now for a byte range `p[0..m * k]` or a
   `k`-byte element range `p[0..m]`), as do element and field addresses
   (`position_in_wide_struct_array`, read by `pointer_formation_in_range`)
   and a field-sized footprint's coverage
   (`memory_range_covers_struct_array_field`). The rule also now refuses a
   negative constant offset whose access ends inside the range. When a
   call's owned memory requirement is missing and the one supplier coverage
   selected is a wide range of another width whose designation matches, the
   refusal names the undecided product
   (`CRuntimeError::WideRangeRespellingMayWrap`,
   `wide_range_respelling_refusal`): ``range `p[0u64..n]` of 8-byte elements
   needs `n * 8` to not wrap (`n * 8 <= UINT64_MAX`)``. It does so only when
   neither re-spelling is decided. Regressions (mdtests):
   `a_callee_owning_a_size_t_struct_range_reads_and_writes_its_fields`
   (`calloc`), `a_callee_writes_fields_of_an_uninitialized_size_t_struct_range`
   (`malloc`), `a_loop_owning_a_size_t_struct_range_writes_its_fields`,
   `a_field_past_a_size_t_struct_range_in_a_callee_is_refused`,
   `a_first_field_one_past_a_size_t_struct_range_in_a_callee_is_refused`,
   `a_field_at_an_unbounded_index_of_a_size_t_struct_range_is_refused`,
   `a_callee_struct_range_longer_than_its_block_is_refused`. Kernel unit tests
   (`tests/resource_tests.rs`):
   `a_wide_struct_range_and_its_byte_range_are_respelled_under_no_wrap`,
   `a_field_access_in_a_wide_struct_range_is_placed_over_its_count`,
   `a_wide_respelling_refusal_names_the_undecided_product`. Scaling
   (`resource_scaling_tests.rs`):
   `respelling_a_wide_struct_range_is_logarithmic_in_unrelated_and_same_block_ranges`.

   Still refused: a byte range a contract spells through a cast,
   `owns (p as (uint8 *))[0..m * 8u64]`, does not supply `owns p[0..m]` to a
   callee, bounded or not: the cast range keeps the cast's designation, which
   the struct requirement's typed carrier does not match. (That is why the
   no-wrap refusal has no mdtest: a byte range over an unbounded count reaches
   a struct requirement only through such a cast.) A 32-bit (`int`) count
   range `p[0..n]` from a `malloc(n * sizeof(struct T))` block with an `int`
   `n` (a wide block) is not supplied either: re-spelling is between wide
   ranges, and the narrow range's bound is not read as the block's
   `uint64` count; the `calloc` form, whose extent is 32-bit, is supplied.

Soundness of (a): a `UInt64` extent `E` is admitted only with `0 < E <= i64::MAX`
decided (raw) or `1 <= n <= i64::MAX / w` and `E = n*w` (element, no wrap, so
`E` is C's `size_t` value); a raw `E` that is a product with a constant `k`
is admitted only with its other factor decided at most `i64::MAX / k`, so
reading it back as elements is exact. Token and range both name `E`; the wide-range
extent guard holds by construction; wide membership makes the scaled offset
mathematical; calloc never evaluates its product; free and realloc consume
exactly the recorded kind and extent. No new trusted assumption
(`docs/concepts/trust.md:57-60, 97-101` already trusts the allocation model).

Out of scope: zero-size allocation, `void *` results, `aligned_alloc`,
`posix_memalign`, blocks above `PTRDIFF_MAX`, non-constant zeroed-prefix
realloc, Integer extents, moving `int32` or constant sizes to the wide kind,
ILP32 targets, C++ `new[]`, the Rust `Vec` model, and the byte-offset
restride.

The fact-dependent lowerings in `roadmap/standard-library.md` stay separate.
The byte-offset restride (`byte_stride_index`, `operators.rs`) has since been
removed: a narrow signed displacement `i * K` keeps its written byte offset,
and the equality graph relates it to element `i` at stride `K` under the
path's `defined(i * K)` fact (`docs/internals/equality-closure.md`). Wide heap
blocks reach that relation only through 32-bit `char` displacements, as
parameter ranges do. Both it and (a) read a `Multiply` as an exact product
only under a decided no-wrap condition.
