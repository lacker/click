# Concurrency profile and first source probe

This is the source-selection checkpoint for the P1
[concurrency demo](../../issues/concurrency-demo.md), not a Click verification
example yet. The synthetic [`fork_join.c`](fork_join.c) is ordinary C11/POSIX
source fixed before its contracts and thread rules are written. It stays here
until Click can verify it; adding an unproved directory under `examples/` would
make the normal example gate fail. The source-integrity test in
`tests/examples.rs` pins its exact bytes. Later example work must use those
bytes, not reshape the C to expose a friendlier proof state.

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
The frozen parent still needs its complete sidecar proof, broader
guarded operations, and the separate native runtime binding described below.

## Selected profile

| Boundary | Selection |
| --- | --- |
| Language and target | C11, x86-64 Linux user space, LP64, eight-bit bytes and `-funsigned-char`. Normal Click verification selects this target when a sidecar declares `target "x86_64-linux-userspace";`, which chooses the include model without `__KERNEL__` and a distinct proof-artifact identity; the kernel target remains the default. Selecting it adds no pthread contract and no concurrency semantics. |
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
are in the selected first probe. The frozen parser regression is not yet a
verified concurrency example.

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

The unchanged probe next stops in `time.h` at `struct sigevent;` with
``unknown struct declaration `sigevent` ``. Incomplete struct forward declarations
are the next full-import step when pursuing a native Linux binding. The
immediate portable slice will use the modeled header with an explicit runtime
assumption and does not depend on parsing glibc headers. Checked create/join
call binding remains subsequent work.

The compiler-backed regression uses the host GCC/header installation and locks
those actual inputs. This run does not establish the selected Debian GCC
12/glibc 2.36 runtime binding; that pinned environment still needs validation.
No header declarations or probe statements are removed.

## Sequential worker checkpoint

`mdtests/fork_join_worker_sequential.md` verifies `fill_range` from this file,
unchanged, with the contract a spawn will transfer as the worker's task. It is
the worker half of the eventual proof, not evidence about threads; the parent
is not yet verified in any form. `mdtests/fork_join_worker_direct_contract.md`
also verifies that same worker with direct `views`/`owns` clauses, so a future
spawn can lend the job record at the call boundary. Its generated certificates
expand and reverify against the unchanged worker.

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

The future Click proof must show the exact contents and ownership for each
outcome, reject overlapping worker write transfers and parent access before
join, and recover each child's result and borrowed job lifetime once. A
companion shared-read-only worker probe belongs in the next implementation
phase. This first checkpoint adds no sequential stand-in, trusted Click
contract, thread rule, or claim that C11 data-race freedom is already modeled.

On the selected Linux toolchain, the source-only syntax check is:

```sh
gcc -std=c11 -pthread -funsigned-char -D_POSIX_C_SOURCE=200809L \
  -Wall -Wextra -Werror -fsyntax-only design/concurrency-probes/fork_join.c
```

The local macOS syntax smoke used Homebrew Clang 19.1.7 with the same source
and options; it is not evidence for the selected Linux ABI or runtime.
