# Language cleanup shortlist

*Parked — out of scope for the current performance-tools project. Revisit when
the owner opens a language arc.*

Keep only these small, high-value cleanup items:

1. **Finish range syntax migration.** Make element ranges such as
   `loadable(p[0..n])` canonical and retire the byte-counting
   `loadable(p, bytes)` form.
2. **Improve proof-failure goal output.** Show unclosed claims and the relevant
   available facts in Surface Click syntax. Choose the CLI or diagnostic
   interface when implementing it.
3. **Clean up memory-clause spelling.** Prefer `owns X` when it is exactly
   equivalent to consuming and returning the same resource, and converge on
   `mutable p->field` instead of `mutable_field(p->field)`.

Do not preserve speculative designs for matching, proof ordering, fact bundles,
resource-state abstraction, framing automation, or unfold/fold search here.
Drive those decisions from the next real-library pilot and concrete proof pain.
