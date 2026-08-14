# Declared resources need symbolic quantities

Click combines repeated equal declared resources into a concrete quantity, but
every `owns`, `consumes`, and `produces` clause still transfers exactly one
unit. A contract cannot create, retain, or consume a runtime-sized number of
units without spelling one clause per unit. This prevents counted-resource
APIs from expressing bulk operations whose logical population changes by a
runtime amount.

The bounded-pool example is the motivating case. Unused capacity should be an
abstract resource:

```click
abstract resource pool_slot(pool: struct pool*);
```

The initial implementation uses refcount as the smaller first regression. Its
`object_ref(obj)` resource already relates a logical population to concrete C
state:

```click
resource object_ref(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    fact obj->refs == count(object_ref(obj));
}
```

Bulk retain should increment `obj->refs` by `amount` and produce `amount`
additional logical references. Bulk nonfinal release should consume `amount`
references while preserving the final owned unit. This exercises symbolic
quantity behavior without introducing a separate source of ghost authority.

## Surface design

Owned declared-resource clauses accept an `int32` coefficient:

```click
produces amount of object_ref(obj);
consumes amount of object_ref(obj);
owns retained of object_ref(obj);
```

An omitted coefficient remains exactly one. `views` does not accept a
coefficient: a view is a copyable core, not a linear quantity. Memory resources
also remain unquantified; multiple copies of exclusive write authority have no
useful meaning. Built-in lifetime authorities such as `allocation(...)` must
retain their existing exclusivity rules.

`owns n of R` captures the entry value of `n` and returns that same quantity;
it must not reevaluate a mutable expression in the post-state and silently mint
or discard units. Explicit `consumes` and `produces` clauses express a genuine
quantity change.

The coefficient is a nonnegative mathematical count represented by a checked
`int32` term. Zero is the additive identity and grants no authority. Click
must not require clients to exclude valid zero-sized states merely to avoid a
conditional implementation case.

## Proof boundary

Each quantity occurrence creates an explicit proof obligation at the snapshot
where that resource clause is evaluated:

```click
0 <= quantity
```

An entry quantity can use certified function requirements. A post-state
quantity can use execution facts and facts proved within that resource claim;
it cannot assume an independently stated `ensures` clause merely because the
contract contains it. Contract application proves the callee's ordinary
requirements before consuming its quantified entry resources.

Resource algebra additionally checks the exact arithmetic needed by an
operation:

- consuming `m of R` from `n of R` requires `m <= n`;
- the residual is the symbolic coefficient `n - m`;
- composing `n of R` with `m of R` produces `n + m` and must certify that the
  nonnegative `int32` representation does not overflow;
- zero residuals confer no view or ownership authority; and
- satisfying a view from quantified ownership requires proof that its
  coefficient is positive.

These are kernel-checked resource facts, not search conventions. Expansion
must emit replayable arithmetic/resource certificates for every selected
operation.

## Kernel representation and efficiency

Quantities remain symbolic coefficients on indexed declared-resource entries.
The implementation must never expand `n of R` into `n` facts or loop over the
numeric value. Exact lookup remains keyed by resource family, name, arity, and
arguments; coefficient arithmetic occurs only after selecting that exact
candidate set.

Normalization, consumption, hashing, substitution, diagnostics, contract
certification, and replay must all preserve the coefficient expression and its
snapshot. A deterministic regression must show that using quantity `1`,
`1_000`, or a symbolic parameter consumes the same resource-algebra work up to
the arithmetic expression size.

## Staged implementation

The first green slice supports symbolic quantities on user-declared abstract
resources and on the nonrecursive population-wide resource exercised by the
refcount example. It establishes the general syntax, coefficient
representation, zero identity, splitting/rejoining algebra, contract
obligations, diagnostics, and certification path. Quantified memory and
allocation resources remain explicitly rejected.

The representation and syntax are general to declared resources rather than a
token-only special case. For resources with population-wide bodies, the
shared body is active exactly when the total coefficient is positive. A
zero-to-positive transition activates it once, and a positive-to-zero
transition finalizes it once. If the current facts cannot decide which
transition occurred, Click requests an explicit positivity obligation rather
than retaining stale body authority or guessing.

Recursive composite quantities require the same population rule and are not a
separate per-unit unfolding mechanism. They remain rejected until the
population transition has a kernel-certified implementation.

## Bounded-pool regression

Extend `examples/bounded-pool` without changing the existing C operations:

```click
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity ==
        pool->checked_out + count(pool_slot(pool))
}
```

- `pool_init` produces `capacity of pool_slot(pool)` from the existing
  `0 <= capacity` requirement.
- `pool_checkout` consumes one slot and produces one `pool_object`; possession
  of the slot replaces the numeric free-capacity precondition.
- `pool_return` consumes one `pool_object` and produces one slot.
- `pool_destroy` consumes `pool->capacity of pool_slot(pool)` after proving the
  pool has no checked-out objects.
- `pool_transfer` produces a source slot, consumes a destination slot, and
  moves the object resource between the pools.
- A zero-capacity init/destroy pipeline proves that `0 of pool_slot(pool)` is
  genuinely the empty resource rather than a hidden token.

The example must continue to preserve the checked-out counter, capacity bound,
object ownership, transfer behavior, and complete lifecycle.

## Focused regressions

- Parse, print, substitute, and type-check quantified declared-resource
  clauses while preserving the unquantified spelling.
- Reject non-`int32` coefficients and unsupported resource families.
- Reject a quantity whose nonnegativity is not proved.
- Accept zero production and consumption without creating usable authority.
- Split one unit from a symbolic quantity and rejoin it without enumerating
  units.
- Reject over-consumption and attempts to derive a view from a quantity not
  proved positive.
- Preserve coefficients through opaque calls, return-resource reconstruction,
  contract certification, expansion, and audit replay.
- Pin deterministic work independently of the coefficient's numeric value.

## Acceptance criteria

- Symbolic quantities are kernel-checked nonnegative coefficients with zero as
  the resource identity.
- No quantity operation performs work proportional to the coefficient's
  runtime value.
- Quantified memory and allocation resources are rejected rather than silently
  applying ordinary declared-resource arithmetic to lifetime authority.
- The bounded-pool slot model verifies unchanged C, including zero capacity,
  ordinary checkout/return, transfer, and destruction.
- Missing arithmetic evidence produces a concise quantity-specific diagnostic,
  not a generic missing-resource dump.
- Generated simple certificates replay, and `click verify`, `click expand`,
  `click audit`, and contract certification agree on every regression.
- `./scripts/check.sh` is green.

## Unblocked (2026-08-14)

The lazy-separation issue closed: the monotonicity regression it demanded
(`added_composition_carrier_keeps_snapshot_premise_work_bounded`) and the
unchanged bounded-pool project are both green on the merged prototype, so
the additional carrier a symbolic quantity introduces no longer breaks
exact-premise replay. This feature can resume.

## First green implementation (2026-08-15)

Symbolic coefficients now cross parsing, lowering, substitution, resource
algebra, opaque calls, exact contract certification, replay, and diagnostics.
The refcount example verifies bulk retain and bulk nonfinal release, and its 29
smart sites all pass expansion audit. A separate abstract-resource regression
passes a symbolic quantity through an opaque call and then consumes it without
minting authority. `./scripts/check.sh` is green.

The issue remains open for the bounded-pool regression, explicit deterministic
work comparison across constant and symbolic coefficient sizes, and any
additional restriction or certification needed before claiming recursive
composite quantities.
