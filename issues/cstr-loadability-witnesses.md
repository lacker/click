# Make C-string witnesses carry dynamic loadability

Found while adding the standard-library `strlen` contract in commit
`7d91fb1a`.

The prelude currently defines `cstr(bytes)` as an existential over
`cstr_len(bytes, len)`. That proposition describes the prefix and terminator
contents, but it does not carry a `loadable(bytes[0..len + 1])` fact. A
variable-length `strlen` contract therefore has no sound way to establish the
range that the external function may read. `choose` can expose some pure
existential witnesses, but the current contract elaborator cannot use a hidden
witness as the endpoint of a later memory segment; contract-level `let` and
witness bindings are also rejected in `loadable` segments.

The current catalog consequently supports only a fixed-footprint empty-string
case for `strlen`. This is a verifier and specification gap, not a reason to
assume that every pointer satisfying a content predicate is readable.

The first bounded slice is now landed: `cstr_len(bytes, len)` carries
`loadable(bytes[0..len + 1])`, and `cstr_len_is_loadable` exposes that fact as a
separate checked theorem. `mdtests/cstr_loadable_witness.md` exercises the
projection. The general existential `cstr(bytes)`/`strlen` call still needs
checked witness selection and dependent range lowering.

## Violated invariant

Every memory-reading external contract must require enough loadability for all
of its possible reads, including a range whose endpoint is discovered through
an existential string-length witness. A C-string abstraction must not turn a
pure content fact about an arbitrary pointer into an implicit memory-safety
guarantee.

## Intended regression

Add an mdtest with an ordinary C function that calls `strlen` on a non-empty,
variable-length byte string and then reads the discovered terminator, for
example:

```c
int32 read_terminator(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return bytes[length];
}
```

Its sidecar should provide a readable C-string precondition, prove the call,
and use the returned length to justify the final read. A paired negative
fixture must show that a content-only string fact, or a string whose
terminator range is not loadable, cannot justify the call or the read.

## Acceptance criteria

- Define a sound witness-carrying string relation, either by extending
  `cstr_len`/`cstr` or by adding a distinct readable-string predicate. The
  relation must include the dynamic loadability range and the prefix/terminator
  conditions; no unrestricted axiom may derive loadability from contents alone.
- Extend existential witness handling so `choose`/equivalent proof steps can
  expose the length and instantiate dependent `loadable(bytes[0..len + 1])`
  facts in the proof state and checked certificate.
- Specify the general external `strlen` contract using that relation, with a
  postcondition tying `result` to the unique terminator length. Prove the
  terminator-length uniqueness theorem from the string conditions rather than
  assuming it as an opaque arithmetic fact.
- Keep memory safety and permission distinct: `loadable` must cover reads,
  while `views`/`owns` continue to govern memory resources and mutation.
- Add positive and negative mdtests, update the language/library
  documentation, and run `scripts/check.sh`.
