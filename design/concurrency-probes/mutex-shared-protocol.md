# Shared mutex protocol for the frozen counter

The [counter source](mutex_counter.c) starts two joinable workers before
joining either one. Each worker locks the same mutex, increments the same
ordinary `value` field, and unlocks. The source is fixed by the integrity test
in `tests/examples.rs`; proof work must not reshape its control flow.

## Required authority

Initialization deposits one folded `counter_state(counter)` instance. Its
identity, definition, and guarded mutex address remain in one protocol
escrow. A worker contract may require a duplicable permission to use that
live protocol. The permission grants no direct memory resource, current
field value, or right to destroy the mutex. Creation checks that the named
protocol exists and gives the worker that permission without copying its
escrowed instance. The parent retains permission to create another worker,
but cannot destroy the mutex while either child can still use it.

Successful lock is an acquire point. It waits for the protocol to be unlocked,
then gives this path the unique folded instance at its current state.
Because another worker may have run, fields and protected memory have to be
freshened consistently with the resource definition. A value read before
unlock remains a fact about that old copy, not a claim about current memory
after a later lock. The holder may unfold, access the ordinary `value` field,
fold, and unlock. Unlock consumes the same instance, checks its declared
invariant, and returns it to the escrow. A second lock in the same path cannot
acquire while its first guard is live. A path without protocol permission
cannot lock, and one without a live guard cannot unlock or touch the field.

The shared protocol cannot be represented by cloning the current
`CState.mutex_ledger`: that ledger contains the folded resource, so two such
copies would each independently own it. Worker verification also cannot
assume a particular previous value: its contract must hold for any state
satisfying the invariant. A generic worker summary must preserve the protocol
and account for its protected-memory effect without handing direct ownership
to the parent before join. The parent may recover the folded instance only
after every potential user has joined and the mutex is destroyed.

## Proof target and first refusals

The first sidecar should prove that each worker's load and store occur under
its checked guard and that both successful creates can be outstanding. A
companion with the increment outside the critical section must fail at that
ordinary access. Further companions must reject a wrong mutex, an unlock
before folding, destruction while a worker is live, and a duplicate guard.
The exact final value of two requires a conserved contribution argument in
addition to this safety protocol; freshening alone deliberately cannot prove
it.

The modeled pthread specification is a trusted runtime assumption. These
rules would validate the C client against that specification, not the native
pthread implementation. The import lock and native binding remain separate.
