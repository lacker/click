# Modeled pthread create/join specification, version 1

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

The C client still owes its worker proof, creation failure paths, ownership
separation, parent access checks, and every source-level continuation. The
checked C transitions implementing this specification are subsequent work;
selecting the model alone grants no create/join behavior.
