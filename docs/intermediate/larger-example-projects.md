# Larger Example Projects

Small proof patterns live in `mdtests/`. Larger verification examples live in
`examples/`.

An example project should look like a tiny library verification effort: ordinary
C files, sidecar specs, and local documentation explaining the proof boundary.

## Current Example

The current project fixture is:

```text
examples/jsonc-refcount/
```

It contains json-c-shaped operations over a one-field object:

- `json_object_get_ref_count`
- `json_object_set_ref_count`
- `json_object_inc_ref_count`

This fixture's proof scope is intentionally narrow:

- one `int32` field in the json-c-shaped struct,
- pointer-to-struct parameters,
- `->` field loads and stores for that first field,
- `views obj->ref_count` for field reads,
- `owns obj->ref_count` for field writes.

This gives Click a realistic shape to verify without pretending it already has
heap allocation or ownership transfer.

## How To Read An Example Project

Read it in this order:

1. Read the project README.
2. Read one C file.
3. Read the matching `.click` sidecar.
4. Compare the sidecar with the closest mdtest.
5. Check which limitation the example is intentionally not solving yet.

The point of an example project is not to be exhaustive. It should make the next
missing feature obvious.

## Relationship To Mdtests

Mdtests are regression tests. They should stay small, self-contained, and easy
to copy when adding a focused feature.

Example projects are larger fixtures. They can have several files and a more
realistic naming style. They should still avoid becoming design sketches: if an
example is under `examples/`, it should verify.
