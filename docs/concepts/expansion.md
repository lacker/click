# Expansion

Expansion replaces a smart proof site with the checked explicit operations that
produced its successful proof state. It turns a heuristic proof request into an
explicit proof script without changing the claim being proved.

The workflow is:

1. Verify the target and retain the proof provenance attributed to the
   selected smart proof site.
2. Extract the surface-expressible explicit operations from that provenance.
3. Render the operations as Surface Click.
4. Replace the selected proof site in output or in place.
5. Verify the complete rewritten source through the ordinary verification
   entry point.

Rewritten-source verification is the boundary. Click must not emit an
expansion merely because search reported success: extraction, rendering,
parsing, and round-trip validation must agree on the resulting proof. An expansion
failure, a rewrite that doesn't verify, or disagreement with profile or audit
is a tooling defect to investigate.

Pure proofs and returning execution paths generate `known()` for direct
computation or an explicit derivation for the remaining work. They do not
generate plain `normalize()`. Selected-premise `normalize() using { ... }`
and divergent-path vacuity still use the legacy normalization forms; an
explicitly written normalization step is preserved.

Generated C branch conditions retain the C operation's meaning. In particular,
a comparison of two data pointers compares their addresses; it does not become
a contract equality of pointer values. When one execution step produces terminal
outcomes needing different closing proofs, expansion can separate them with an
explicit proof case whose condition each checked outcome decides.

Library references in the output must resolve in the rewritten file. Expansion
preserves explicit full paths and uses short module paths only when their
modules are in scope. If a rewritten full path supplied a library module,
expansion retains that module with an explicit import when the certificate
uses a bare declaration name, including resource names such as `cstr_at`.
A theorem application with no declared prerequisites
and value arguments is already a simple operation and is not an automation
site for audit or profile. Produced application certificates retain their
explicit `using` block, including an empty block: an empty list alone does not
mean that the theorem declares no prerequisites. Computed arguments retain their definedness obligations
and may still need premise search.

Expansion removes planning and search from that site, which improves
reproducibility, makes the chosen operations reviewable, and should recover
approximately all performance available from checking those choices directly.
The explicit proof still pays for parsing its text and for the unavoidable
semantic work of each operation, so a tiny smart tactic need not become
measurably faster. Expansion doesn't guarantee that the explicit proof is the
clearest possible proof, and it cannot remedy an inefficient simple checker;
a materially slow simple leaf is a verifier defect.

For syntax, selection, and output behavior, see [`click expand`](../reference/cli/expand.md).
