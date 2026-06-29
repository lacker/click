# jsonc-mini Pilot

This directory is the first frozen real-library-shaped pilot target. The
matching mdtests are `mdtests/jsonc_mini_ref_count_getter.md` and
`mdtests/jsonc_mini_ref_count_setter.md`.

The fixture starts with two json-c-shaped operations:

- `json_object_get_ref_count`: read a reference-count field from a small object.
- `json_object_set_ref_count`: write and return the reference-count field.

The first proved properties are simple: under a valid-object precondition, the
getter returns the object's `ref_count` field without mutating externally
visible memory, and the setter writes only that field-sized footprint.

The current support is intentionally narrow:

- one `int32` field per struct
- pointer-to-struct parameters
- `->` field loads and stores for that first field
- `valid_field(obj->ref_count)` as the field-validity precondition
- `mutable_field(obj->ref_count)` for field writes

Keep this pilot narrow. Add the smallest C0, memory-model, and proof features
needed by this fixture before broadening to heap allocation or ownership
transfer.
