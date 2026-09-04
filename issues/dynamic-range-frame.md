# Add a smart tactic for dynamic range framing

The dynamic C-string read regression currently requires the caller to expose a
terminator-length witness and write the matching `views` range explicitly.
`cstr_readable` supplies an existential content/loadability witness, but it is
not itself a permission or ownership resource. This issue covers the proof
language feature that can connect those two facts ergonomically.

## Violated invariant

Every indexed C read must be justified by a resource covering the concrete
cell that the execution may access. A smart tactic may select a witness from
an existential predicate and split or reframe an already-owned compatible
range, but it must never manufacture `views` or `owns` permission from
`loadable` or from a pure C-string predicate alone.

The tactic must produce a checked, expandable certificate. Its search must be
bounded by the named witness and candidate resource, rather than scanning or
cloning unrelated proof state.

## Intended regression

Use the unchanged C source from
`mdtests/cstr_dynamic_indexed_read.md`:

```c
int32 read_terminator(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return bytes[length];
}
```

Add a sidecar regression in which the caller supplies an existing compatible
resource for the C-string storage, states `requires cstr_readable(bytes)`,
and invokes the new smart tactic. The tactic should select the existential
length, establish the dynamic `views bytes[0..length + 1]` range, and let the
`strlen` result justify the indexed read using
`cstr_readable_len_unique`.

Add negative coverage showing that the tactic rejects all of the following:

- `cstr_readable(bytes)` or `loadable(...)` without a permission resource;
- a resource whose endpoint cannot cover the selected terminator cell; and
- an overlapping or otherwise incompatible resource transformation.

The existing explicit positive and permission-negative fixtures remain the
small baseline while this ergonomic form is developed.

## Acceptance criteria

- Define and document the smart tactic's surface form, witness-selection
  rules, compatible `views`/`owns` inputs, and failure diagnostics.
- The positive dynamic C-string regression verifies with the tactic and its
  certificate expands into checked simple framing and witness steps.
- Negative regressions prove that missing or incompatible permission fails;
  `loadable` and pure content facts never become permission implicitly.
- The tactic is bounded and output-sensitive, and the kernel validates the
  generated certificate without reproducing smart search.
- Update the tactic and C-string documentation, add the regression to the
  example catalog where appropriate, and run `scripts/check.sh`.
