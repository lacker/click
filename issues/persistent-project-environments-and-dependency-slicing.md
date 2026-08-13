# Project verification clones global environments and imports global theorems

For each selected function, `verification.rs` clones the complete
`CExecutionEnvironment`, then clones it again for contract certification.
`CExecutionEnvironment` owns complete function bodies and verified rules.
Separately, every verified scalar theorem is copied into every function's
certification facts, even when the function and its dependencies never refer
to it.

This permits quadratic project behavior: adding an unrelated function or
theorem increases the cost of verifying every existing function. Exact
function lookup is indexed, but environment construction and certification
input are not dependency-local.

## Required design

Make the immutable project environment structurally shared. Per-function loop
rules and temporary recursive hypotheses should be overlays whose creation is
constant or logarithmic in the overlay size. Give each function a deterministic
dependency closure containing only callable rules, referenced resources,
predicates, layouts, and theorem facts.

Dependency slicing must remain conservative and sound. A missing dependency
must be a deterministic construction error, never an excuse to fall back to
the global environment or to trust a caller-provided theorem.

## Regression design

Generate projects containing a fixed one-step target plus increasing numbers
of unrelated functions and unrelated scalar theorems. Verify the target by
location and verify the whole project. Target verification should be flat up
to lookup factors; whole-project work should grow linearly with total source.

## Acceptance criteria

- Creating a per-function environment does not clone unrelated function
  bodies or verified rules.
- A function's certification fact set contains only its theorem dependency
  closure.
- Targeted verification is insensitive to unrelated project growth.
- Whole-project simple verification passes the project-size scaling gate.
- Recursive hypotheses and loop-rule overlays retain their current kernel
  authority boundaries.
