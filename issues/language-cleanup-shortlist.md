# Language cleanup shortlist

Remaining small, high-value cleanup items:

1. **Clean up memory-clause spelling.** Prefer `owns X` when it is exactly
   equivalent to consuming and returning the same resource, and converge on
   `mutable p->field` instead of `mutable_field(p->field)`.

Do not preserve speculative designs for matching, proof ordering, fact bundles,
resource-state abstraction, framing automation, or unfold/fold search here.
Drive those decisions from the next real-library pilot and concrete proof pain.
