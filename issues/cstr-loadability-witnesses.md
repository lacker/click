# Complete dynamic C-string reads and witness uniqueness

The first dynamic-loadability slice is now landed. `cstr_readable_len` carries
the nonnegative length, prefix/terminator conditions, and
`loadable(bytes[0..len + 1])`; `cstr_readable` packages that relation behind an
existential witness. The checked `strlen` contract uses the relation, and the
prover can transport wider ranges into guarded universal and existential
loadability propositions. The focused regressions are
`mdtests/cstr_dynamic_loadability.md`, `mdtests/forall_loadable_range.md`, and
`mdtests/exists_loadable_range.md`.

The remaining gap is the next step after `strlen`: a caller that uses the
returned symbolic length for an actual C array read still needs a matching
`views`/`owns` resource. `loadable` is intentionally not permission, so the
current `strlen` slice proves dynamic read safety for the external call and
its result relation but does not manufacture a dynamic permission range. The
contract also does not yet expose a checked uniqueness theorem for the
terminator length.

## Violated invariant

Every memory-reading external contract must require enough loadability for all
of its possible reads, including a range whose endpoint is discovered through
an existential string-length witness. A C-string abstraction must not turn a
pure content fact about an arbitrary pointer into an implicit memory-safety or
permission guarantee.

## Intended regression

Extend the ordinary C example so it reads the discovered terminator:

```c
int32 read_terminator(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return bytes[length];
}
```

Its sidecar should provide a readable C-string precondition plus an explicitly
framed permission/resource, then use the returned length to justify the final
read. A paired negative fixture must show that `cstr` or `loadable` alone does
not authorize a resource-sensitive access.

## Acceptance criteria

- Add checked support for deriving a dynamic `views`/`owns` range from an
  explicitly framed allocation or resource and the selected string witness;
  do not infer permission from `loadable`.
- Specify and prove a terminator-length uniqueness theorem from the readable
  string conditions rather than assuming it as an opaque arithmetic fact.
- Add positive and negative mdtests for the post-`strlen` symbolic read and
  permission distinction, update the language/library documentation, and run
  `scripts/check.sh`.
