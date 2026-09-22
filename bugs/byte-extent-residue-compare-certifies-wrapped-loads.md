# Byte-extent residue comparison can certify a wrapped loadability coverage

P1. Machine integers may not be silently read as mathematical or unsigned
values; byte extents are counts, and a residue is not a count.

## What was found

`loadable_covered_by_fact` (`src/kernel/api/contract_certification.rs:300`)
certifies a loadability goal from a wider assumed fact by forming
`end = Add(delta_bytes, bytes)` — a 32-bit machine add — and deciding
`certification_proves_signed_le(end, span)`:
`signed_bitvector_constant` compares the *residues* as `int32`. When
`delta + bytes` exceeds `2^32`, the residue can sit at or below `span` while
the true end is past the fact's span, so the route reports a covering that
does not exist. Statically confirmed by reading the route:
- byte extents are legal surface counts up to `u32::MAX / element_width`
  (`src/kernel/primitives/contracts.rs` "fits" guard), so a `bytes` word of
  `0x80000000` is in-surface;
- `delta_bytes` is produced by `pointer_offset_byte_delta`
  (contract_certification.rs:169) without a bound below `2^31`;
- the deciding comparison (`certification_proves_signed_le`,
  contract_certification.rs:387) compares wrapped residues.

The sibling routes compare extent constants only after binding the count to
its validity guard (`constant_range_extent`,
`src/kernel/primitives/resource_algebra.rs:5250`; the loadability extent
guards in
`src/kernel/assumptions/memory_reasoning.rs`). This route has no visible
respectable bound at the point of decision — the deciding line is exactly
the wrap boundary the bughunt hazard list names ("Index arithmetic wraps at
32 bits; pointer byte offsets are exact i64").

## Scenario

A contract context with assumed fact `loadable(q, 0x40000000)` and a goal
`loadable(p, 0x80000000)` where the goal base sits at a byte displacement
`0x80000001` from the fact's base such that `delta + bytes` folds to
`1`: the rule's signed answer says the goal end is inside the span while
the true byte end is 3 GiB past it. The deciding answer is the machine
residue, not the mathematical extent.

Also present in the same rule: the additive-constant-strip fallback at
contract_certification.rs:334 casts the stripped shifts as `i32` and
compares them (`(end_shift as i32) <= (span_shift as i32)`), which reads two
`u32` residues as signed — same class.

## Intended regression

A unit test at `contract_certification.rs` level constructing the goal and
assumed fact above (constants via `Bitvector32Term::Constant`, goal base
`fact_base.offset_by_bytes(delta)`) must be *refused* by
`loadable_covered_by_fact` unless the caller proved `delta + bytes <= span`
mathematically (e.g. by exact `i64` delta arithmetic or by refusing any
involving extent/displacement whose 32-bit word needs a wrap to stay in
`[0, 2^31)`).

## Acceptance

- [ ] The covered-by-fact route decides in-bounds using exact byte counts or
      a bound at the deciding line, with the wrapped-extent regression
      refusing.
- [ ] `scripts/check.sh` green.
