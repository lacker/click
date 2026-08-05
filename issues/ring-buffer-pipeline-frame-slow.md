# Expand the slow ring-buffer pipeline frame

## Problem

`ring_buffer_pipeline.contract` has a successful SMART `frame` at statement 5
taking about 3.4 seconds exclusive, above the two-second smart budget. The
project is quarantined until the expansion workflow succeeds and the rewritten
proof is fast.

## Work

Use the profiler's exact source location with `click-expand`. Verify and
reprofile the emitted artifact, then run the audit fixed-point check. A failed
expansion, replay mismatch, or slow simple replacement is a tooling bug and
takes priority over manually editing the frame certificate.

## Acceptance criteria

- The smart frame is replaced by an accepted deterministic certificate or its
  search is reduced below budget.
- No simple replacement crosses 500ms.
- Cold verification and audit expansion both pass.
- Ring-buffer is removed from quarantine in the same change.
