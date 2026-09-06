# Prove copied union-member views in contracts

The C0/kernel execution path preserves overlapping typed union-member views
when a struct containing a supported union is copied by value. The contract
certifier can currently prove ordinary fields across that boundary, but it
does not establish a postcondition relating a copied union-member load to the
source member load. The user-facing proof therefore stops short of expressing
the strongest property already established by the kernel execution regression.

## Violated invariant

A contract over a supported union-containing by-value struct should be able to
state that a scalar or pointer member read from the returned/copy aggregate is
equal to the corresponding member read from the source aggregate, subject to
the existing read-only union and resource preconditions. The proof should use
the typed overlay identity, not treat the overlapping members as disjoint
ordinary cells.

## Intended regression

An unchanged C fixture passes a struct containing `union { int32 number;
int32* pointer; }` by value and returns it. A Click contract states both
`result.tag == value.tag` and `result.payload.number == value.payload.number`
and verifies with `auto` under explicit readability/resource preconditions.
A pointer-member version checks that the copied member preserves pointer
identity and provenance.

## Acceptance criteria

- Contract certification derives equality for supported scalar and pointer
  union-member loads across parameter, local-copy, and return boundaries.
- The derivation uses the existing typed union overlay and preserves the
  containing allocation/provenance; it does not flatten overlapping members or
  introduce an active-member assumption.
- Missing readability, unsupported member types, union writes, whole-union
  values, and compiler-dependent reinterpretation remain rejected.
- The intended mdtests pass and `scripts/check.sh` remains green.

Related: [struct-model.md](struct-model.md) and
[multiple-compilers.md](multiple-compilers.md).
