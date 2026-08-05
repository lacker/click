# Speed up the perpetual-service simple frame

## Problem

`service_run.loop(0).effect_2` contains a deterministic SIMPLE `frame` taking
about 0.7 seconds exclusive, above the 500ms budget. A slow simple tactic is an
engine bug and must not be expanded.

## Work

Reduce the frame's exact resource context and determine whether repeated
composite-resource separation, recursive service ownership, or effect-range
matching dominates replay. Add a kernel-level count/budget regression around
the identified deterministic path.

## Acceptance criteria

- The frame replays below 500ms on the development baseline.
- Its certificate and resource result are unchanged.
- The project is removed from quarantine in the same change.
