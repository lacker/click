# json-c Refcount Pilot

This directory is the first frozen library-shaped example project. Each C file
has a matching `.click` sidecar in this directory. Focused self-contained
regressions for the same features live in `mdtests/jsonc_refcount_getter.md`,
`mdtests/jsonc_refcount_setter.md`, and `mdtests/jsonc_refcount_increment.md`.

The fixture starts with three json-c-shaped operations:

- `json_object_get_ref_count`: read a reference-count field from a small object.
- `json_object_set_ref_count`: write and return the reference-count field.
- `json_object_inc_ref_count`: increment and return the reference-count field.

The first proved properties are simple: under a valid-object precondition, the
getter returns the object's `ref_count` field without mutating externally
visible memory, the setter writes only that field-sized footprint, and the
increment helper proves the expected old-to-new count relation under a
no-overflow precondition.

The current support is intentionally narrow:

- one `int32` field in the json-c-shaped struct
- pointer-to-struct parameters
- `->` field loads and stores for that first field
- `loadable(obj->ref_count)` as the field-loadability precondition
- `read(obj[0..1])` or `write(obj[0..1])` as the access permission
- `mutable obj->ref_count` for field writes

Keep this pilot narrow. Add the smallest C0, memory-model, and proof features
needed by this fixture before broadening to heap allocation or ownership
transfer.
