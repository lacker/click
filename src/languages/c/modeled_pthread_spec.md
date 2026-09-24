# Modeled pthread create/join and mutex specification, version 2

This trusted specification is an explicit assumption of a conditional Click
client proof. It does not certify an operating system's pthread implementation.

- `pthread_create` evaluates its arguments once. With null attributes and a
  direct verified, terminating worker, a zero result creates one joinable child,
  transfers the worker's checked task resources, and stores a handle in the
  caller's authorized output slot. A nonzero result creates no child and leaves
  those task resources with the caller. The output slot is unspecified on
  failure. The parent cannot use the worker's returned resources or
  postconditions before a checked join.
- `pthread_join` accepts a live handle for this parent's unique joinable child
  with exact termination evidence, no detach, cancellation, competing join, or
  self-join. Under those preconditions the runtime join succeeds, consumes the
  one completion right, and makes that child's checked output delta and
  postconditions available. The initial binding requires a null result slot.
- Handles are C values associated with an unforgeable creation identity.
  Copies preserve that identity but never duplicate its completion right.
  Integer representations alone grant no thread authority.
- `pthread_mutex_init` with null attributes and a selected folded, exclusive
  resource whose `guarded_by` field is the passed mutex address succeeds and
  deposits that resource in the mutex. This model treats the mutex bytes as
  opaque and tracks initialization through unique proof authority.
- `pthread_mutex_lock` succeeds for an initialized, unlocked mutex and gives
  the current path its escrowed resource. `pthread_mutex_unlock` succeeds only
  when that same resource has been folded and returned to escrow.
  `pthread_mutex_destroy` succeeds only for an unlocked initialized mutex and
  returns its resource to the caller. These calls do not branch on a failure
  status under their checked preconditions.

The checked mutex transitions currently apply to one C path with no worker
sharing. Creation of a worker while a mutex is initialized is refused.
Every initialized mutex must be destroyed before its C function returns.

The C client still owes its worker proof, creation failure paths, ownership
separation, parent access checks, and every source-level continuation. The
current checked C transition supports one unresolved creation at a time,
scalar local work and an owner-authorized store to disjoint external memory
before its status test, and a checked join after the status selects success.
Other intervening operations and additional pending creates are refused until
their guarded authority can be represented and checked.
