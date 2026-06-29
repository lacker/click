# jsonc-mini Pilot

This directory is the first frozen real-library-shaped pilot target. The
matching mdtest is `mdtests/jsonc_mini_ref_count_getter.md`.

The fixture starts with one json-c-shaped operation:

- `json_object_get_ref_count`: read a reference-count field from a small object.

The first proved property is simple: under a valid-object precondition, the
function returns the object's `ref_count` field and does not mutate externally
visible memory.

The current support is intentionally narrow:

- one `int32` field per struct
- pointer-to-struct parameters
- `->` field loads for that first field
- byte-level `valid_range(obj, 4)` as the validity precondition

Keep this pilot narrow. Add the smallest C0, memory-model, and proof features
needed by this fixture before broadening to heap allocation or ownership
transfer.
