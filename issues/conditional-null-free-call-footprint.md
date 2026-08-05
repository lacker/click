# Apply null free contracts without evaluating invalid footprints

## Problem

`conditional_resource_branchless_free.md` verifies `free(NULL)` through a
conditional resource, but the opaque caller `destroy_null()` fails while
applying `item_destroy(0)`. Contract application tries to evaluate a mutable
segment base and produces `TypeMismatch` even though the null branch contains
no allocation or memory body and `free(NULL)` is a no-op.

The resource condition and null conversion should determine which footprint is
active before the verifier demands evaluation of memory that does not exist.

## Intended design

- Evaluate conditional resource and effect guards before evaluating their
  guarded pointer/range expressions.
- A statically null call should instantiate only the empty branch.
- Do not interpret an ill-typed or non-loadable expression in an inactive
  branch as a runtime error.
- Preserve local errors for active malformed footprints.

## Regression

Keep the existing mdtest as the integration regression and add a smaller
contract-application unit test with a null argument, conditional allocation
resource, and guarded mutable range. Add a nonnull negative companion proving
that active invalid footprints still fail.

## Acceptance criteria

- `destroy_null()` verifies through the opaque `item_destroy(0)` call.
- Inactive conditional footprints are not evaluated.
- Nonnull invalid footprints retain an actionable local diagnostic.
- The mdtest leaves quarantine.
