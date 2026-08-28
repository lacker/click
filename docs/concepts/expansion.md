# Expansion

Expansion replaces a smart proof site with the checked explicit operations that
produced its successful proof state. It turns a heuristic proof request into an
explicit proof script without changing the claim being proved.

The workflow is:

1. Verify the target and retain the checked transition history attributed to
   the selected smart proof site.
2. Extract the surface-expressible explicit operations from that history.
3. Render the operations as Surface Click.
4. Replace the selected proof site in output or in place.
5. Verify the complete rewritten source through the ordinary verification
   entry point.

Rewritten-source verification is the boundary. Click must not emit an
expansion merely because search reported success: extraction, rendering,
parsing, and round-trip validation must agree on the resulting proof. An expansion
failure, a rewrite that doesn't verify, or disagreement with profile or audit
is a tooling defect to investigate.

Expansion removes search from that site, which improves reproducibility and
makes the chosen operations reviewable. It doesn't guarantee that the explicit
proof is the clearest possible proof, and it doesn't remedy an inefficient
simple checker.

For syntax, selection, and output behavior, see [`click expand`](../reference/cli/expand.md).
