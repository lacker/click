# Complete dynamic C-string reads and witness uniqueness

The first dynamic-loadability slice is now landed. `cstr_readable_len` carries
the nonnegative length, prefix/terminator conditions, and
`loadable(bytes[0..len + 1])`; `cstr_readable` packages that relation behind an
existential witness. The checked `strlen` contract uses the relation, and the
prover can transport wider ranges into guarded universal and existential
loadability propositions. The focused regressions are
`mdtests/cstr_dynamic_loadability.md`, `mdtests/forall_loadable_range.md`, and
`mdtests/exists_loadable_range.md`.

The post-`strlen` indexed-read slice is now covered by
`mdtests/cstr_dynamic_indexed_read.md`: the caller supplies an independently
known witness and matching dynamic `views` range, then uses the checked
`cstr_readable_len_unique` theorem to connect that witness to the returned
length. `mdtests/cstr_dynamic_indexed_read_requires_permission.md` preserves
the distinction between readable contents and permission. A remaining
ergonomic gap is deriving the dynamic permission range automatically from an
existential `cstr_readable` witness; callers currently need to expose a
matching length and frame explicitly.

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
  do not infer permission from `loadable`. (The current slice requires the
  caller to provide that frame explicitly.)
- [x] Specify and prove a terminator-length uniqueness theorem from the
  readable string conditions rather than assuming it as an opaque arithmetic
  fact.
- [x] Add positive and negative mdtests for the post-`strlen` symbolic read
  and permission distinction, and update the language/library documentation.
- Run `scripts/check.sh` before closing the remaining framing gap.
