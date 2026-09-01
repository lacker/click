# Verify one unchanged existing-source fixture

`examples/README.md:33-35` states that every project in the tree is
synthetic and that "the first unchanged-source fixture is tracked in
`issues/audit-existing-c-source-fidelity.md`." That file did not exist until
the 2026-09-01 kernel audit at cb034b21 noted the dangling reference. This is
that issue.

The headline capability claim, that Click verifies unchanged real-world C,
currently has neither a fixture nor an open item. The audit's gap list
explains why: the C0 frontend rejects standard type spellings, includes,
multi-function files, calls in expressions, `else if`, `break`, and most of
the integer model, so no third-party file parses today. This issue is the
end-to-end acceptance target those items serve.

## Violated invariant

`examples/` must contain at least one project whose C source is an identified
upstream file preserved byte-for-byte, with a `SOURCE.md` and a checked
source-integrity manifest, verified under the normal examples gate.

## Intended regression

Choose one small, self-contained upstream C function or file (a candidate is
a leaf helper from json-c such as a reference-count or buffer-length routine,
matching the roadmap's pilot target) and add it unchanged under
`examples/<name>/` with `SOURCE.md` naming the upstream commit and path, a
manifest the examples gate checks against the file contents, and a sidecar
that verifies at least one memory-safety contract for it. Until the frontend
gaps close, the project may carry a parser-only qualification, but the file
must be present and byte-identical from the start so the gap list is
measured against it.

## Acceptance criteria

- The fixture exists, the integrity manifest is enforced by
  `tests/examples.rs`, and any edit to the imported C fails the gate.
- `examples/README.md` points at the fixture instead of this issue.
- The fixture's parser and verification status is reported by the examples
  gate, and each frontend issue it is blocked on is linked from
  `SOURCE.md`.
- When the fixture verifies under the normal gate, `scripts/check.sh` passes
  and this issue is deleted.

Related: [c-type-spellings.md](c-type-spellings.md),
[multi-function-files-and-headers.md](multi-function-files-and-headers.md),
[calls-in-expressions.md](calls-in-expressions.md),
[c-syntax-conveniences.md](c-syntax-conveniences.md),
[integer-types.md](integer-types.md).
