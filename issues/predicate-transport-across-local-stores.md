# Guide opaque predicate transport through definitions

## Problem

At a frontier reached after initializing stack locals, a predicate over
unchanged external memory may be definitionally the same fact as at function
entry. An opaque kernel predicate cannot soundly be transported merely because
the C touched only a local: its definition is what identifies the memory it
observes. Smart `transport` currently explores that opaque transport and then
reports a certificate-oriented failure:

```text
could not make fact transport premises explicit:
explicit surface premises do not replay the certified fact transport
```

The concrete `loop_sorted_range_invariant` proof now takes the principled
explicit path: unfold `sorted` and `sorted_range` at entry, carry the expanded
definition over the immutable loop, and close the postcondition from that
definition. Its frontier proof and every smart site pass `click audit`.

The remaining problem is ergonomic. `transport` should not imply that an
opaque predicate can be framed directly and then fail with internal
certificate vocabulary. It should promptly explain that the predicate must be
unfolded so Click can see its footprint, or perform that checked unfolding
itself and emit the corresponding surface certificate.

## Minimal regression

Require an opaque predicate over `int32 p[3]`, execute only local declaration
and assignment statements, then request direct smart transport of the entry
predicate to the current frontier.

## Acceptance criteria

- Smart transport either unfolds the predicate definition and emits a freshly
  replayable surface certificate, or promptly explains that the writer must
  unfold it before transport.
- No internal memory summary or opaque-predicate frame axiom becomes
  assumable.
- The explicit unfolded proof remains green and expansion-auditable.
