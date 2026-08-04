# Perpetual service

This project demonstrates partial correctness for a service loop that is not
supposed to return.

`service_init` constructs a composite `service` resource owning both the
service metadata and its separate backing cell. `service_step` toggles a
two-state protocol and returns the same folded resource. `service_run` calls
that verified function opaquely inside `while (1)`; its loop invariant records
the legal phase range while the resource is transferred to and returned by
each summarized call.

Click proves that every finite execution prefix is free of the checked forms of
undefined behavior, respects the declared memory footprint, preserves the
composite ownership invariant, and keeps the phase and backing cell in a legal
state. The lack of a return frontier is intentional.

This is not a liveness theorem. The model does not claim that another service
step eventually occurs, that a scheduler is fair, or that any external input
or output trace is productive. Those properties require temporal and
environment semantics that this example does not invent.
