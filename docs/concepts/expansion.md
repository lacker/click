# Expansion

Expansion replaces a smart proof site with the simple tactics in its replayable
certificate. It turns a heuristic proof request into an explicit proof script
without changing the claim being proved.

The workflow is:

1. Verify the target and let the smart tactic construct a certificate.
2. Replay the certificate from the proof site's initial state.
3. Render its simple steps as Surface Click.
4. Replace the selected proof site in output or in place.
5. Verify the expanded source again.

Replayability is the boundary. Click must not emit an expansion merely because
search reported success; the certificate and printed rewrite must verify. An
expansion failure, a rewrite that doesn't verify, or disagreement with profile
or audit is a tooling defect to investigate.

Expansion removes search from that site, which improves reproducibility and
makes the chosen operations reviewable. It doesn't guarantee that the explicit
proof is the clearest possible proof, and it doesn't remedy an inefficient
simple checker.

For syntax, selection, and output behavior, see [`click expand`](../reference/cli/expand.md).
