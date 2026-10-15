# Final assumption discards its failure trace

Soundness: incomplete. An existing proof failure loses the checked context
needed by the opt-in trace. This does not demonstrate false acceptance.

On the object-model recovery archive, the original string-clear proof rejects
its final `owner->data[0] == 0` claim. Both the original project and the
[single-function reduction](final-assumption-discards-failure-trace/repro.md)
report `proof trace unavailable: no checked path was retained for this failure`:

```sh
click verify --trace-proof owned_string_clear \
  bugs/final-assumption-discards-failure-trace/repro.md
```

The preceding unfold, three execution steps, explicit `have` proofs and fold
check. The trace should preserve those recorded operations and the selected
failed goal's existing diagnostic context, using the current renderer. No new
fact discovery or additional diagnostic presentation is requested.

The post-execution assumption driver drops each failed focused proof error and
then creates a fresh summary error. Investigate whether that discards the
existing context; this source observation is not yet a checked repair.

Acceptance criteria:

- This failure retains its checked path and selected goal in the opt-in trace.
- Preserve rejection, summary wording, output limits and existing rendering.
- Cover a failed final assumption with earlier successful checked tactics;
  no diagnostic-only fact may participate in checking.
- Remove private probes and retain the original clear C and contract.
