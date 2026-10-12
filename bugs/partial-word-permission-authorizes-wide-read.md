# Four bytes of permission authorize an eight-byte read

Read authority must cover the complete physical access. The legacy logical
field exception in `authorized_access_element_length` instead counts every
eight-byte access as one element of a four-byte range. This affects pointer
cells and other eight-byte values: the query receives only a byte width.

## Reproduction

The regression
`kernel::functions::native_span_inputs::tests::native_loaded_prefix_requires_full_initialized_pointer_cell_read`
reproduced this during the bounded object-model work. It declares and
initializes an eight-byte pointer cell, grants a view of only its first four
bytes, and evaluates the native typed pointer load while requiring owned
expression reads. The load succeeds and can supply a native input witness.
The partial-permission assertion failed in the focused test run on 2026-10-11.

The essential permission query can also be reproduced directly: a resource
range with element width four and endpoints `0..1` authorizes an eight-byte
read at its base. It must refuse; `0..2` is the corresponding positive case.

## Acceptance

- Require the complete physical width for permission and candidate queries.
- Reject partial pointer-cell permission even when the entire cell is live
  and initialized; initialization cannot supply missing authority.
- Preserve reads authorized by complete pointer, wide scalar, and byte ranges.
- Preserve complete-width framing and checked resource/proof operations.
- Remove the historical logical-field exception and its misleading comments.
