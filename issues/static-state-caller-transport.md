# Transport current static state through cross-file callers

## Violated invariant

After ordinary function entry stops restoring mutable static initializers, a
caller with explicit current-value preconditions must be able to transport
those facts through earlier calls and satisfy a later cross-file callee
precondition. The caller must not lose unchanged scalar, aggregate, or
function-local static facts merely because another static object was updated.

## Intended regression

Restore the `examples/multifile-registry/` sidecar as a passing example after
its mutable static contracts state the current values explicitly. The
registry updates two file-scope statics, two function-local statics, and
cross-file aggregate fields before reading the state again.

## Acceptance criteria

- `CLICK_EXAMPLE=multifile-registry cargo nextest run --test examples` passes
  without relying on initializer values at ordinary function entry.
- The sidecar keeps explicit current-value preconditions and does not change
  the C sources to expose verifier-only state.
- The unfiltered examples gate no longer quarantines `multifile-registry`.
