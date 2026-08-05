# Expand slow field-derived load preservation

## Problem

`field_derived_precise_effect_after_metadata_write.md` has a successful SMART
`have` in `buffer_push_preserves_first` taking about 5.1 seconds, well above the
two-second budget. The claim transports an unchanged first element across an
opaque call whose mutable range is derived from metadata.

This is closely related to the semantic wart in
`opaque-call-unchanged-loads.md`, but it is independently actionable as a slow
successful proof site.

## Work

Attempt normal expansion first and require parse, replay, cold verification,
reprofile, and audit fixed-point success. If the generated certificate is huge
or fails replay, fix the tooling/unchanged-load issue rather than retaining a
large ambient-fact dump in the mdtest.

## Acceptance criteria

- The site is below the smart budget or becomes a sub-500ms simple certificate.
- The proof still demonstrates precise field-derived effect preservation.
- Expansion and audit succeed.
- The mdtest leaves quarantine.
