# Bounded Pool

This project verifies the original pool C with explicit population authorities.
The C stores capacity and checkout count; individual objects retain their own
private memory. The C source is verified unchanged.

`pool_storage(pool)` packages ordinary pool memory and the empty authorities
for `pool_slot(pool)` and `pool_object(pool, _)`. The caller establishes those
authorities at the pool's allocation lifetime and passes them explicitly;
initialization of an external pointer cannot create them. `pool_init` consumes
storage and produces `pool_control(pool)` plus the requested nonnegative slot
quantity.

The control owns pool memory and both authorities. Its facts say that checkout
count equals the object population and capacity equals checked-out objects plus
available slots. `valid_pool(pool)` states the same pure invariant. Global
counts are observed under the corresponding authority, including checked
observations through a folded control. Count facts alone grant no member rights.

Checkout consumes a slot and ordinary object memory, producing the concrete
`pool_object(pool, object)` member while preserving the object's value. A member
owns its own private object memory: its contents can be opened and written while
the pool control stays closed. Return consumes that exact member under the
control's authority, restores ordinary memory, and produces a slot. Transfer
borrows both controls, consumes the source member and destination slot, then
produces the destination member and source slot. All four effects have separate
authority, identity, quantity, and custody checks.

Growth produces a symbolic nonnegative slot quantity and requires the original
C addition to be defined. Shrink consumes its supplied slot quantity, including
zero, and preserves other slots and checked-out members. Their arithmetic proofs
establish signed bounds and restore conservation without treating a global
count as ownership. Cleanup consumes the complete available-slot batch, proves
both populations empty, retires both authorities, and returns ordinary pool
memory. Authority retirement does not free the C allocation.

The original two-object pipeline checks out both objects, writes values 11/22
through their private members, returns them in reverse order, and cleans up.
The zero-capacity and resize pipelines check empty quantities and retirement.
The transfer pipeline initializes two pools, checks out an object, and moves it
between them through ordinary helper contracts. It returns both controls, the
destination member, and the source slot, preserving the object's value. Storage
and control openings establish the memory separation needed across calls.

Run `click verify examples/bounded-pool` from the repository root. The sidecar
contains 16 checked claims: five arithmetic lemmas and all eleven original C
functions. The arithmetic lemmas and the counter steps inside the functions
are `by auto`: the solver carries the `int32` facts to `Integer`, proves each
addition or subtraction defined, and closes every bound and conservation
equation by a checked certificate, which `click expand` prints.
