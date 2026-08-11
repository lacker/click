# Perpetual-service `fold` runs at its simple budget and fails nondeterministically

`service_step.contract` in `examples/perpetual-service` verifies or fails
depending on ambient machine load. Repeated `target/debug/click verify
examples/perpetual-service` runs on one machine produced, with no source or
binary change in between:

- clean verification;
- `tactic budget exhausted: tactic `fold` in `service_step.contract` exceeded
  its 500ms simple real-time limit after 0.500s (statement 4, source tactic
  5); a slow simple tactic is a Click engine bug`; and
- `` `fold(service(owner))` requires an exact body fact: missing pure fact:
  separate(memory(owner[0..4]), memory(owner[...])) `` where the reported
  available-fact list contains a fact that prints identically to the missing
  one.

The failures reproduce most readily while the machine is otherwise busy (for
example during a parallel `cargo test` run); quiet runs typically pass. This
is unrelated to smart-tactic search: `fold` is a simple tactic and its work
must be proportional to its certificate.

Two violated invariants:

- A simple tactic must fit its class budget with margin; a `fold` that spends
  ~500ms matching resource body facts is a Click performance bug regardless of
  whether it finishes.
- A diagnostic must be stable and actionable. The "missing pure fact" variant
  lists an identically printed fact as available, which suggests the exact
  body-fact match falls back to a deadline- or fuel-bounded equivalence pass
  whose truncation is then misreported as a missing fact.

## Reproduction

```sh
target/debug/click verify examples/perpetual-service
```

Run repeatedly under CPU load (or during `cargo test`) until a failure
appears. Statement 4's `fold(service(owner))` after the branch in
`service_step` is the affected site.

## Acceptance criteria

- `fold(service(owner))` in `service_step.contract` completes well inside the
  simple-tactic budget on a loaded machine, with a profile showing the match
  cost proportional to the resource body.
- The exact body-fact check either matches deterministically or reports the
  actual spelling difference; it never reports a fact as missing while an
  identically printed fact is listed as available.
- A regression pins the body-fact matching cost or determinism for a fold
  whose body facts require snapshot-respelled `separate` evidence.
