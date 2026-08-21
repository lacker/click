# The verification pipeline

Click verifies existing C against declarations in a `.click` sidecar. The
pipeline keeps convenient user syntax separate from the small operations that
ultimately justify acceptance.

1. The project loader finds the C source named by `verifying` and resolves the
   selected target.
2. The C0 and Click parsers build source-level syntax trees with source spans.
3. Validation resolves names, checks types and declaration rules, and rejects
   unsupported C or Click forms.
4. Elaboration makes contextual Surface Click meaning explicit, including
   snapshots, C fragments, resources, and proof-site identity.
5. Lowering translates propositions, contracts, and executable operations to
   Kernel Click structures.
6. Proof construction interprets explicit tactics or lets bounded smart
   planners propose simple steps.
7. Replay checks those steps from the initial proof state. Kernel operations
   justify symbolic execution, proposition reasoning, and memory/resource
   transitions.
8. Diagnostics map failures and work attribution back to source locations.

The crucial boundary is between proposing a proof and checking it. A smart
tactic may be incomplete or change its search strategy without becoming part
of the trust argument. Its success matters only when the resulting simple
certificate replays.

Ordinary verification establishes correctness first. [`click profile`](../reference/cli/profile.md)
then attributes work in a successful or intentionally diagnosed run;
[`click expand`](../reference/cli/expand.md) materializes replayable simple
steps; and [`click audit`](../reference/cli/audit.md) checks the combined
workflow under repository policy.

See [Surface Click and Kernel Click](surface-and-kernel.md) for the two
representations and [Internals](../internals/index.md) for module ownership.
