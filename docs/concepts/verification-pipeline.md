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
6. Proof checking interprets explicit tactics as checked transitions over the
   current proof state. Bounded smart tactics search by trying those same
   transitions on persistent alternatives.
7. Kernel operations justify symbolic execution, proposition reasoning, and
   memory or resource transitions. A smart success is a completed checked
   proof state, not an unchecked search result.
8. Diagnostics map failures and work attribution back to source locations.

The crucial boundary is between proposing a proof and checking it. A smart
tactic may be incomplete or change its search strategy without becoming part
of the trust argument. It can advance a proof only through the same checked
operations available to explicit tactics.

Ordinary verification establishes correctness first. [`click profile`](../reference/cli/profile.md)
then attributes work in a successful or intentionally diagnosed run;
[`click expand`](../reference/cli/expand.md) materializes the checked operations
chosen at a smart site as an explicit proof and verifies the rewritten source;
and [`click audit`](../reference/cli/audit.md) checks the combined workflow under
repository policy.

See [Surface Click and Kernel Click](surface-and-kernel.md) for the two
representations and [Internals](../internals/index.md) for module ownership.
