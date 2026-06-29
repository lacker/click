# jsonc-mini Pilot

This directory is the first frozen real-library-shaped pilot target. It is not
expected to verify yet. The matching mdtest is
`mdtests/jsonc_mini_struct_field_unsupported.md`, which records the current
front-end boundary.

The fixture starts with one json-c-shaped operation:

- `json_object_get_ref_count`: read a reference-count field from a small object.

The intended first property is simple: under a valid-object precondition, the
function returns the object's `ref_count` field and does not mutate externally
visible memory.

The first missing features are:

- C0 struct declarations.
- Pointer-to-struct parameters.
- `->` field loads.
- Field-level memory validity and frame facts.

Keep this pilot narrow. Add the smallest C0, memory-model, and proof features
needed by this fixture before broadening to heap allocation or ownership
transfer.
