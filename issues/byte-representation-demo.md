# P1: Byte representation demo

## Objective and violated invariant

Requested on 2026-09-15 as a before-launch architecture milestone. Verify a
small C program that copies an object's representation into a byte buffer and
back, preserving its scalar values and pointer identity. This tests whether
typed values, byte access, initialization, and allocation provenance compose
in the memory model. Owning a byte range does not by itself establish a valid
typed value, and copying a pointer's representation must neither erase its
origin nor manufacture access authority for its pointee.

Rbtree remains the main launch demo. This milestone supplies narrow evidence
about representation copying, not a claim of general type punning or arbitrary
pointer fabrication.

## Intended regression

Use an ordinary C struct with an unsigned integer field and an object-pointer
field. Initialize it with a symbolic scalar and a pointer to a live object,
copy all `sizeof` bytes into an `unsigned char` buffer, then copy those bytes
into a distinct, correctly aligned object of the original struct type. Read
the restored fields and dereference the restored pointer using separately
held pointee authority. Prove exact scalar equality, pointer identity, and
the expected pointee value. Copying the pointer does not copy its pointee.

Choose and record one C standard and supported compiler/target profile before
implementation. Use defined representation-copy operations, such as `memcpy`,
under that profile. Preserve the selected source before writing its sidecar;
do not replace byte copies with field assignments or add proof-only C. Small
synthetic code is acceptable when its provenance is explicit.

Verify the copying helper's body if it is included in the claim. A supported
standard-library primitive may instead have an explicit trusted specification
with kernel-checked effects; that is verification of its client, not a proof
of libc. Bind the actual declaration/builtin and profile rather than recognizing
an arbitrary user function by name. Do not hard-code the demo struct layout
or require its fields to have constant values.

## Required model boundaries

- Distinguish storage lifetime, initialized representation, typed load
  validity, and permission to access it. Explain the selected C rules for the
  destination object and copying bytes that include padding.
- Preserve representation information through the intermediate byte buffer
  and modular calls. Copying padding need not assign it a stable mathematical
  value; do not prove whole-struct byte equality from field equality alone.
- A byte write overlapping a known typed cell invalidates or updates the
  affected observation. Typed and byte views cannot become independent,
  contradictory descriptions of the same storage.
- Preserve pointer allocation identity through an intact representation copy.
  Restoring a representation does not restore a freed allocation's lifetime,
  establish pointee ownership, or validate an arbitrary sequence of bytes as
  an invented pointer.
- Copy checked ranges and their relevant representation information locally.
  A fixed-size copy must not scan every allocation or old memory snapshot.

## Negative and companion regressions

- Out-of-bounds copy and overlap passed to a non-overlapping copy primitive
  fail their actual access/precondition checks.
- Reading an uninitialized required field after an incomplete copy is refused.
- Copying into live read-only storage or storage protected by an independent
  stable borrow is refused.
- A restored pointer cannot authorize a pointee load without its resource;
  using a saved pointer representation after freeing the pointee is refused.
- A checked write to the unsigned scalar's representation cannot leave the
  old scalar value unconditionally provable. Choose a defined byte mutation
  under the pinned profile and prove the corresponding changed observation.
- Malformed or unsupported pointer representations receive bounded refusals;
  no guessed pointer origin or unchecked type reinterpretation is accepted.

## Acceptance criteria and dependencies

- The original C and modular sidecars verify the complete round trip and
  pointee observation. Exact layout/profile assumptions and any trusted copy
  primitive are documented and retained in import/certificate identity.
- Negative and companion regressions exercise representation, authority,
  lifetime, and overlapping-observation boundaries for their intended reasons.
- The production kernel checks the rules, with a durable design record of
  their semantics and the relationship between bytes and typed cells.
- Normal verify, expand/reverify, profile, and audit agree on the original
  source. No alternate representation-only verifier is introduced.
- Add deterministic scaling regressions at four or more sizes for copied
  extent/representation metadata and for a fixed copy surrounded by unrelated
  memory. Charge work to explicit inputs and produced state/certificate delta
  under the [efficiency contract](../docs/internals/verification-efficiency.md).
- Positive and negative fixtures are in the normal gate; `scripts/check.sh`
  passes. Delete this issue and its list entry when implementation,
  regressions, and durable documentation land.

Reuse existing byte-range ownership, typed memory, and import identity. This
does not depend on C++, concurrency, or goto. General effective-type changes,
arbitrary union punning, arbitrary pointer/integer reconstruction, a target
matrix, and byte-layout reallocation remain outside the milestone. Follow
`AGENTS.md` if proof tooling exposes a blocker.
