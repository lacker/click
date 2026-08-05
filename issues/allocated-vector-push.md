# Compose in-capacity append with allocated-vector growth

## Purpose

The repository now verifies three independent capabilities:

- a general in-capacity append from any `0 <= len < cap`;
- positive runtime-sized `int32` allocation and direct deallocation; and
- malloc-copy-install-free growth that preserves the live prefix.

The next useful composition test is the operation a real owning vector exposes:
append directly when capacity remains, otherwise grow and then append. This is
not a request for a new resource algebra. It should first test whether the
current exclusive allocation, memory, and composite-resource rules compose
naturally.

## C behavior

Use ordinary C control flow:

1. If `len == cap`, call the verified growth helper.
2. If allocation fails, return failure without changing the vector.
3. Write the new value at `data[len]`.
4. Increment `len` and return success.

Do not duplicate the copy loop, require a caller to preselect the branch, add
save/restore assignments for proof purposes, or replace direct helper calls
with allocation-specific wrappers.

The first version may retain the current `cap + 1` growth policy. Geometric
growth and its additional multiplication/overflow reasoning are separate work.

## Contract

The operation consumes and produces `allocated_vector(owner)` and establishes:

- result is failure or success;
- failure preserves length, capacity, data pointer, allocation authority, and
  every live element;
- success increases length by exactly one;
- success stores the requested value at `old(len)`;
- success preserves every element in the old live prefix;
- capacity and the backing pointer remain unchanged on the in-capacity path;
- after either successful path, the produced allocation is live, owned, and
  large enough for the new length.

Choose a clear policy for the maximum supported capacity. A simple entry
precondition matching `vector_grow` is acceptable for this composition slice;
handling maximum capacity as a third runtime outcome should be a separate
design if desired.

## Resource composition

Prefer reusing the checked in-capacity append and growth contracts rather than
re-proving their C bodies inside the combined function. If the focused
`vector_push` resource shape cannot be called while retaining allocation
authority, adapt its contract or add a narrow allocation-owning interface in a
separate comprehensible change. Do not weaken allocation lifetime checking or
copy the same ownership facts into unrelated ad-hoc resources.

Any awkward unfold/fold sequence or inability to retain the allocation token
across an in-capacity call is evidence about Click's resource interface and
should become its own focused tooling or language issue before changing the C.

## Verification

- Cover three paths: spare capacity, full capacity with failed allocation, and
  full capacity with successful allocation.
- Keep a focused value-preservation regression for both successful paths.
- Verify and profile the completed proof unit with native Click deadlines.
- Audit every smart site introduced or changed by the composition and require
  expansion replay and fixed-point success.
- Keep the owned-vector README explicit about the `+1` capacity policy.

## Acceptance criteria

- Natural grow-or-append C verifies without proof-driven source edits.
- All three runtime paths satisfy the exact resource and value contract.
- The implementation reuses verified helper contracts rather than inlining
  their proofs semantically.
- No new resource algebra is added unless a separately documented minimal
  counterexample demonstrates that the existing model cannot express the
  composition.
- The project stays within ordinary tactic and sidecar limits, and profile
  diagnoses any remaining cost accurately.
