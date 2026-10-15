# Final assumption discards its failure trace

Soundness: incomplete. An existing proof failure loses the checked context
needed by the opt-in trace. This does not demonstrate false acceptance.

The [minimal reproduction](final-assumption-discards-failure-trace/repro.md)
correctly rejects a deliberately false postcondition after checking a store
and a true stored-value fact. Its final `assumption` reports
`proof trace unavailable: no checked path was retained for this failure`:

```sh
click verify --trace-proof f bugs/final-assumption-discards-failure-trace/repro.md
```

The recovery archive also reproduces this on the unchanged
[string-clear C and contract](final-assumption-discards-failure-trace/string-clear.md).
Its preceding unfold, execution steps, explicit `have` proofs and fold check.
The trace should preserve those recorded operations and the selected failed
goal's existing diagnostic context, using the current renderer. No new fact
discovery or additional diagnostic presentation is requested.

The post-execution assumption driver drops each failed focused proof error and
then creates a fresh summary error. Investigate whether that discards the
existing context; this source observation is not yet a checked repair.

Acceptance criteria:

- This failure retains its checked path and selected goal in the opt-in trace.
- Preserve rejection, summary wording, output limits and existing rendering.
- Cover a failed final assumption with earlier successful checked tactics;
  no diagnostic-only fact may participate in checking.
- Remove private probes and retain the original clear C and contract.

## Checked repair candidate

Retain the focused failure's diagnostic context on the original driver summary,
and register the focused root under its existing checked trace prefix. The
current renderer then shows the earlier store and successful `have` before the
failed goal; no facts are synthesized for diagnostics. All 125 focused
surface-diagnostic, proof-trace and proof-diagnostic controls pass, including a
regression preserving the driver summary and rejecting the false claim.
The original string-clear trace also exposes its already checked
`terminated_at(..., 0)` fact; explicit predicate elimination closes that proof.
Current-upstream extraction remains pending.
