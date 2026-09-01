# Fail loudly on load-variable capacity and clear the proved cache per session

Found by the 2026-09-01 kernel audit at cb034b21. Neither item has a known
untrusted-input exploit today; both remove a guard the kernel explicitly
relies on for soundness rather than for performance.

1. **Registry clear.** Load-variable ids are a 40-bit fold of the
   epoch-substituted snapshot and the pointer
   (`src/kernel/eval/memory_loads.rs:572-579`, `:1283-1291`). The defining
   equations `Var(id) == load(mem, ptr)` are treated as ambient truths and
   filtered out of premises (`src/kernel/reasoning/path_facts.rs:36`, `:80`),
   so their truth rests entirely on injectivity, which only the registry's
   `assert!(known == memory && known == pointer)` (`memory_loads.rs:1294-1298`)
   enforces; the doc comment at `:1268-1270` says exactly this.
   `load_variable_for_cell_with_origin` clears the whole registry at
   1_000_000 entries (`:1300-1302`) before inserting, so a colliding pair
   that straddles the clear is silently conflated: both defining facts
   circulate and `canonical_term` maps two distinct loads to one variable. At
   the 1M operating point the 40-bit birthday collision probability is about
   36%. The registry is per `VerificationSession`, which spans a whole
   project verify call plus continuation environments
   (`src/surface/verification.rs:552-558`). Pre-clear variables also lose
   their registry entries, degrading completeness.
2. **PROVED cache.** The thread-local cache in
   `certification_proves_context_free_forall`
   (`src/kernel/api/contract_certification.rs:2695`) is not in the clear list
   of `VerificationSession::enter` (`src/kernel/mod.rs:110-125`). Ids and
   embedded snapshots are content-addressed, so a cached closed universal
   keeps its truth value across sessions unless a hash collision occurs, but
   the cache bypasses the registry's in-session collision assertion: a
   cross-session collision would be accepted silently for a cached fact
   instead of panicking.

## Violated invariant

Each reserved load-variable id represents exactly one load identity for the
lifetime of every fact that mentions it. Anything cached as proved from the
empty context must be re-derived, or at least re-validated, within the
session whose thread-local state it depends on.

## Intended regression

Kernel unit test: inside one `VerificationSession`, register load identity
`A`, mint enough distinct filler identities to reach the capacity threshold,
then register a distinct identity `B` whose id equals `A`'s (construct the
pair offline or lower the threshold under `cfg(test)`). Today no panic fires
and both calls return the same variable. After the fix the kernel must
fail verification loudly at capacity (or before) rather than clear, and the
collision must still be detected.

Second test: a fact cached by `certification_proves_context_free_forall` in
one session is not returned from the cache in a fresh session.

## Acceptance criteria

- The registry never clears mid-session; reaching capacity is a reported
  verifier failure (`ExecutionLimit`-style), not silence.
- The context-free-forall cache is cleared in `VerificationSession::enter`
  alongside the other per-session tables.
- Both tests above; `scripts/check.sh` passes.
