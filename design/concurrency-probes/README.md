# Concurrency profile and verified fork/join probe

This records the source selection and runtime boundary for the P1
[concurrency demo](../../issues/concurrency-demo.md). The synthetic
[`fork_join.c`](../../examples/concurrency-fork-join/fork_join.c) is ordinary
C11/POSIX source fixed before its contracts and thread rules were written.
Its [Click sidecar](../../examples/concurrency-fork-join/fork_join.click) now
verifies both the worker and parent under the explicit modeled pthread runtime.
The normal example gate verifies that project, and the source-integrity test
in `tests/examples.rs` pins the C bytes.

The [mutex counter source](mutex_counter.c) is frozen separately. Its two
workers mutate the same ordinary cell under one lock. The
[shared-protocol design](mutex-shared-protocol.md) records the authority and
interference rules needed to verify it; the current one-path mutex escrow
still refuses worker creation while that mutex is initialized.

The [mutex parity source](mutex_held_parity.c) is a quarantined C probe for a
smaller open proof boundary. For a successful initialization and valid mutex
operations, its loop holds the mutex exactly when `i` is odd, then unlocks
and destroys it before returning. The source is intentionally outside the
example and mdtest gates: no Click sidecar proves it yet. The current loop
checker carries one concrete mutex ownership status at a loop head and cannot
represent this conditional status. Future proof work should keep these C
bytes fixed and establish the parity relation for arbitrary `n`, including
zero and both final parities. It must also reject a false parity relation or
an unlock on an unheld path.

## Binding direction

The [pthread binding design](pthread-binding-design.md) describes how ordinary
C create/join calls use the existing worker contracts, `step`, and `branch`.
The modeled-runtime identity and a first checked C create/join path now run on
macOS. One pending creation may survive scalar local work and an
owner-authorized store to disjoint external memory before a C branch chooses
success or failure. Two sequential creates over disjoint task cells now verify
all three parent outcomes, including the second failure's cleanup join and
both successful join orders. Source regressions reject abandoning the first
completion on second failure and reading a child's cell before its join. The
parent can now split one explicit stable view between two read-only workers;
their source proof covers both join orders and cleanup after a failed second
create. The same sharing now works for a parent stack cell without an
ownership annotation, and rejects writes or scope exit while a reader lives.
An explicitly owned cell can likewise back both readers; the owner returns
only after the final join, including when joins occur in reverse order.
The frozen parent has a complete sidecar proof. Broader guarded operations and
the separate native runtime binding described below remain future work.

## Selected profile

| Boundary | Selection |
| --- | --- |
| Language and target | C11, x86-64 Linux user space, LP64, eight-bit bytes and `-funsigned-char`. The example project selects `x86_64-linux-userspace` in `click.project.json`, which chooses the include model without `__KERNEL__` and a distinct proof-artifact identity. The same config explicitly selects `modeled-pthread`; target selection alone supplies no thread semantics. |
| Compiler and C library | Debian Bookworm GCC 12.2.0, glibc 2.36 headers and pthread runtime. The eventual locked import must record the exact driver, headers, flags, and ABI observations; the current modeled declarations are not that lock. |
| Compile options | `-std=c11 -pthread -funsigned-char -D_POSIX_C_SOURCE=200809L`. No optimizer- or scheduler-specific ordering assumption belongs in a proof. |
| Thread API | The selected `pthread.h` declarations for `pthread_create` and `pthread_join`, with joinable threads only. The declaration projection spells `pthread_t` as its x86-64 ABI `unsigned long`; checked modeled rules treat its value as a handle rather than deriving thread behavior from integer arithmetic. Spawn success creates exactly one child and a completion handle; failure creates none. A successful join consumes that handle exactly once. |
| Later mutex API | `pthread_mutex_init`, `pthread_mutex_lock`, `pthread_mutex_unlock`, and `pthread_mutex_destroy` on one ordinary POSIX mutex, with checked guard/resource transfer. No recursive mutex, condition variable, cancellation, detach, or signal operation. |
| Later atomic subset | C11 `_Atomic int` with `atomic_init`, `atomic_store_explicit(..., memory_order_release)`, and `atomic_load_explicit(..., memory_order_acquire)` for one-shot publication. No read-modify-write, fence, relaxed protocol, or implicit strengthening to sequential consistency. |

The first Click import is a declaration-only projection of `<pthread.h>` and
`<stddef.h>` sufficient to parse the frozen source unchanged. The separate
modeled runtime supplies checked create/join transitions under an explicit
assumption; the declarations themselves supply no pthread external contracts
or scheduler semantics. Only null attributes and null join-result arguments
are in the selected first probe. The frozen source is now a verified modeled
concurrency example; the native pthread binding remains unverified.

The pthread implementation is a trusted runtime boundary, not a verified C
body. Its future specification must identify these exact declarations and
types, including the source profile and import lock. A valid joinable handle
held only by this parent, with no detach, cancellation, competing join, or
self-join, is assumed to join successfully; this assumption must be scoped to
those preconditions by a checked rule. Thread creation may fail and must not
transfer ownership on failure. The thread body and both client paths remain
verification obligations. A native compiler run below checks C syntax only;
it does not establish any concurrency property.

## Compiler-import checkpoint

Compiler-backed imports now accept the user-space target with a fixed C11,
LP64, unsigned-char, pthread/POSIX profile. Include roots remain explicit and
inventoried. The sidecar and prepared import must select the same target;
changed headers, profiles, and stale locks are rejected. This is import
support only, not a pthread runtime binding or a concurrent proof.

`tests/compiler_import.rs` prepares the unchanged probe through real GCC/glibc
headers and checks the bounded parser refusal. On this implementation host
(Ubuntu GCC 13.3.0 and glibc 2.39), preparation and lock loading succeed.
The original parser gap, `typedef unsigned short int __u_short;`, is fixed:
standard short/long integer spellings now accept their optional trailing `int`
with the existing widths and signedness. Parser regressions and
`mdtests/c_integer_trailing_int.md` pin that behavior.

The `signed char` typedef for `__int8_t` now lowers to the distinct signed
byte type `int8`, with one-byte storage, integer promotion, and checked
conversions in the range -128 through 127. The explicit `signed int` spelling
also now maps to the existing `int32` type in C and Click declarations,
including typedefs, pointers, casts, and `sizeof`. `mdtests/c_signed_int.md`
pins its normal verification behavior.

The anonymous struct typedef for `__fsid_t` now imports unchanged:
`typedef struct { int __val[2]; } __fsid_t;`. It reuses the named-struct layout
rules, with a private identity for each declaration. The typedef can name
local values and pointers without inventing a visible C tag.
`mdtests/c_anonymous_struct_typedef.md` checks its eight-byte layout, field
access, and independent copies.

GCC's `typedef __SIZE_TYPE__ size_t;` now imports unchanged as well. On
this host, the macro expands to `long unsigned int`. C and Click share the
same parser for valid standard integer specifier combinations, regardless of
order; `mdtests/c_integer_specifier_order.md` checks their existing widths
and signedness.

Inline arrays of signed and unsigned 64-bit integers now retain their
eight-byte layout through indexing, resource clauses, initialization, and
struct copies. `mdtests/struct_wide_integer_arrays.md` checks those paths.

The `cpu_set_t` dimension `1024 / (8 * sizeof(__cpu_mask))` now imports
unchanged, producing sixteen eight-byte words. Scalar and embedded-struct
array dimensions reuse the typed integer constant evaluator; positive lengths
and checked layout sizes remain required. The regression
`mdtests/struct_constant_array_lengths.md` checks the original dimension,
multidimensional indexing, and embedded-struct copies.

GNU `nothrow` and `__nothrow__` annotations now import on function
prototypes and definitions, including comma-separated lists and repeated
attribute groups. They supply no proof facts in the C model: bodies and
memory effects remain checked normally. `mdtests/c_nothrow_attributes.md`
and its ownership-rejection companion pin this behavior.

GNU `leaf` and `__leaf__` are now accepted too, so the combined
`__attribute__((__nothrow__, __leaf__))` produced by glibc's `__THROW`
imports unchanged. Click does not use `leaf` to infer purity, absence of
callbacks, or memory permissions. `mdtests/c_leaf_attributes.md` checks a
cross-file call with normal ownership and postconditions.

The `const char *__tm_zone` field of `struct tm` now imports unchanged.
Struct fields retain first-level pointee constness through reads, initializers,
copies, and calls, while rejecting writes through that pointer or implicit
const removal. The pointer member remains assignable; const qualification
does not freeze memory reachable through mutable aliases.
`mdtests/const_pointer_fields.md` checks those distinctions.

The unchanged probe's Ubuntu GCC 13/glibc 2.39 preprocessed artifact is now
committed as a locked fixture and loaded in the Mac gate without GCC or Linux
headers. Bare `struct sigevent;` forward declarations now parse without
inventing a layout. Fixed pointer arrays in structs now import, including the
member in `bits/types/__locale_t.h:30`. Anonymous and inline tagged union
typedefs now retain their complete member layout, including arrays and nested
structs; compound union member operations remain bounded refusals pending
typed access and copy support. Pointer uses of the aligned typedef
`__pthread_unwind_buf_t` now import; value storage still refuses until its
alignment is represented in allocation and aggregate layout. The frozen import
now recognizes the x86-64 `long double` size and alignment needed by
`max_align_t`. Unused glibc external object declarations no longer require
definitions in the verified source bundle, so the frozen artifact loads
through the ordinary import path on macOS. The existing worker and parent
sidecar now verifies against that locked artifact under the explicitly
selected modeled pthread runtime; the binding checks the locked
`/usr/include/pthread.h` declaration origin and parameter types.
Weak linkage, asm symbol labels, and returns-twice annotations
import with their limits retained; calls needing symbol availability or a
returns-twice control-flow model are refused. GCC `access`, `const`,
`nonnull`, `noreturn`, and `deprecated` annotations and standard or GNU
`restrict` syntax import without granting proof facts. The modeled proof remains
separate from native runtime validation; the imported headers alone grant no
pthread semantics.

The compiler-backed regression uses the host GCC/header installation and locks
those actual inputs. This run does not establish the selected Debian GCC
12/glibc 2.36 runtime binding; that pinned environment still needs validation.
No header declarations or probe statements are removed.

## Sequential worker checkpoint

`mdtests/fork_join_worker_sequential.md` verifies `fill_range` from the frozen
source with the contract a spawn transfers as the worker's task. That earlier
sequential proof alone made no concurrency claim.
`mdtests/fork_join_worker_direct_contract.md` verifies the same worker with
direct `views`/`owns` clauses; its generated certificates expand and reverify.
The complete example sidecar uses that direct contract for its checked spawns.

## Frozen fork/join program

`fill_parallel` requires a live four-element output array. The parent zeros
it before starting either thread. `fill_range` is one reusable worker over a
half-open interval: one child writes indices `[0, 2)` to 11, and the other
writes `[2, 4)` to 22. The stack-allocated job records and the output array
remain live until every created child is joined. On success the function
returns 1 with output `[11, 11, 22, 22]`. If the first creation fails it
returns 0 with all zeros; if the second fails it joins the first before
returning 0 with `[11, 11, 0, 0]`. There is no parent read after spawn or
free/return of a child-borrowed object before its join.

The [example](../../examples/concurrency-fork-join/) proves the exact output
contents for all three outcomes and ownership of the output buffer at return.
The modeled create/join rules transfer disjoint output slices, borrow each
stack job until join, and reject overlapping writes or premature parent access.
Shared-reader companions and hostile source regressions exercise both join
orders, cleanup, and refusals. These are conditional client claims under the
trusted modeled pthread runtime specification, not a native Linux or macOS
runtime validation.

On the selected Linux toolchain, the source-only syntax check is:

```sh
gcc -std=c11 -pthread -funsigned-char -D_POSIX_C_SOURCE=200809L \
  -Wall -Wextra -Werror -fsyntax-only examples/concurrency-fork-join/fork_join.c
```

The local macOS syntax smoke used Homebrew Clang 19.1.7 with the same source
and options; it is not evidence for the selected Linux ABI or runtime.
