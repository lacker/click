# Concurrency profile and first source probe

This is the source-selection checkpoint for the P1
[concurrency demo](../../issues/concurrency-demo.md), not a Click verification
example yet. The synthetic [`fork_join.c`](fork_join.c) is ordinary C11/POSIX
source fixed before its contracts and thread rules are written. It stays here
until Click can verify it; adding an unproved directory under `examples/` would
make the normal example gate fail. The source-integrity test in
`tests/examples.rs` pins its exact bytes. Later example work must use those
bytes, not reshape the C to expose a friendlier proof state.

## Selected profile

| Boundary | Selection |
| --- | --- |
| Language and target | C11, x86-64 Linux user space, LP64, eight-bit bytes and `-funsigned-char`. This needs a distinct user-space Click target identity; the existing `x86_64-linux-kernel` profile injects `__KERNEL__` and must not be reused for glibc headers. |
| Compiler and C library | Debian Bookworm GCC 12.2.0, glibc 2.36 headers and pthread runtime. The eventual locked import must record the exact driver, headers, flags, and ABI observations; no lock or supported Click profile exists yet. |
| Compile options | `-std=c11 -pthread -funsigned-char -D_POSIX_C_SOURCE=200809L`. No optimizer- or scheduler-specific ordering assumption belongs in a proof. |
| Thread API | The selected `pthread.h` declarations for `pthread_create` and `pthread_join`, with joinable threads only. `pthread_t` is opaque to Click even if this ABI represents it as an integer. Spawn success creates exactly one child and a completion handle; failure creates none. A successful join consumes that handle exactly once. |
| Later mutex API | `pthread_mutex_init`, `pthread_mutex_lock`, `pthread_mutex_unlock`, and `pthread_mutex_destroy` on one ordinary POSIX mutex, with checked guard/resource transfer. No recursive mutex, condition variable, cancellation, detach, or signal operation. |
| Later atomic subset | C11 `_Atomic int` with `atomic_init`, `atomic_store_explicit(..., memory_order_release)`, and `atomic_load_explicit(..., memory_order_acquire)` for one-shot publication. No read-modify-write, fence, relaxed protocol, or implicit strengthening to sequential consistency. |

The pthread implementation is a trusted runtime boundary, not a verified C
body. Its future specification must identify these exact declarations and
types, including the source profile and import lock. A valid joinable handle
held only by this parent, with no detach, cancellation, competing join, or
self-join, is assumed to join successfully; this assumption must be scoped to
those preconditions by a checked rule. Thread creation may fail and must not
transfer ownership on failure. The thread body and both client paths remain
verification obligations. A native compiler run below checks C syntax only;
it does not establish any concurrency property.

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
