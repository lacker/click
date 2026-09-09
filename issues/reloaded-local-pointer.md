# Preserve aliases for pointers reloaded from caller-visible memory

**Severity: high.** After a call, a pointer loaded back out of caller-visible
memory must still be able to alias the local object whose address was stored
there. Otherwise a state can prove `q == &x` while a store through `q` leaves
`x` unchanged.

**Violated invariant.** A pointer value loaded from memory may designate any
object consistent with the established pointer-equality facts, including an
automatic local. Pointer identity must not be inherited from the storage cell
that contained the pointer.

**Fix.** Canonicalize a pointer value materialized from caller-visible memory
after a call-havoc edge as a symbolic pointer identity, rather than inheriting
the storage cell's block. When an exact alias fact relates that pointer to a
local slot, resolve the lvalue to the local slot before checking resources or
applying the store.

**Regression coverage.**

- `mdtests/reloaded_local_pointer_alias.md` verifies the true result `2`.
- `mdtests/reloaded_local_pointer_impossible.md` rejects the inconsistent
  result claim `7`.

**Acceptance criteria.**

- The positive sidecar proves that the reloaded pointer aliases `x` and that
  the store through it changes the returned value to `2`.
- The inconsistency sidecar is rejected; no execution of the same C program
  may verify `result == 7`.
- Existing pointer-load, memory-havoc, resource, and canonicalization tests
  continue to pass.
