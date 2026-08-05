# Compose runtime allocation into owned-vector growth

## Purpose

Finish the user-visible operation that motivated runtime-sized allocation:
grow a full owned vector by allocating new storage, copying live elements,
installing it, and freeing the old allocation.

The runtime allocation kernel slice, standalone runtime allocation/free
example, and general vector-push example are the check-in checkpoint. The copy
helper and growth composition remain pending. Growth must wait for the blocking
ownership/effect/certificate issues linked from the issues README; it must not
land as an unverified example or depend on artificial C rewrites.

## C behavior

Use ordinary malloc-copy-free C:

1. Save the old capacity and data pointer.
2. Allocate a checked positive runtime capacity, initially `old_cap + 1` for a
   small proof surface.
3. On null, return failure with the original vector unchanged.
4. Copy `len` elements to the new allocation.
5. Install the new pointer and capacity.
6. Directly free the old pointer.
7. Return success.

Do not require redundant save/restore of unchanged length, a pointer-inequality
branch that real malloc semantics already guarantee, or a wrapper solely to
make direct `free` pass effect checking.

## Resource design

Define an allocated vector resource that owns metadata plus
`allocated_int32s(owner->data, owner->cap)`. Copying must have a documented
borrow/ownership boundary that leaves no stale view. On failure, restore the
original composite unchanged. On success, consume the old lifetime and fold the
new allocation into the vector.

The contract should guarantee:

- result is failure or success;
- failure preserves length, capacity, pointer, allocation, and contents;
- success preserves length and live element values;
- success installs the requested larger capacity and a live owned allocation;
- the old allocation cannot be accessed after success.

## Verification

- Add focused mdtests for the helper-call resource composition before restoring
  `vector_grow` to the example.
- Verify and profile the proof unit. No tactic may cross its class budget.
- Run `click-expand` on every smart site used by growth and require replay and
  audit fixed-point success.
- Keep normal diagnostics compact under intentionally broken variants.

## Acceptance criteria

- Natural malloc-copy-direct-free C verifies without proof-driven source edits.
- Both allocation branches certify exact effects and resources.
- Value preservation covers the copied live prefix.
- The owned-vector project remains unquarantined and completes within the
  normal project budget.
- Its README describes only behavior present in the checked example.
