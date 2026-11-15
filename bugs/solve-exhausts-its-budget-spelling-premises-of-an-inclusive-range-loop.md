# `solve` exhausts its budget spelling premises of an inclusive-range loop

Soundness: incomplete. A true back-edge member is refused after the smart
work budget runs out; no false claim verifies.

The back-edge closer of a two-line inclusive-range loop runs `solve` out of
its 2,000,000-unit budget (about 10 s in a debug build) on the member
`total + 1 == 256` of the pass that exhausts the range, instead of closing
it or failing promptly. `CLICK_TIMINGS=1` attributes the work to premise
spelling: about 3.5M units in `solve closure: premise spelling` over 62
calls, and about 400 calls of `solve premise surface at recorded
states` / `across recorded states`. The refusal names the member by a
compiler temporary, `__rust_mir_10 == 256`.

## Reproduction

`design/charon-trial/inclusive-ranges` (unchanged Rust source and lock), with
`every_byte`'s proof replaced by:

```click
fn every_byte() -> u32 {
    ensures result == 256u32;
} by {
    step_until(loop(0));
    loop {
        decreases 256u32 - total;
        invariant iter_end == 255u8;
        invariant total <= 256u32;
        invariant iter_done == 0 implies total == (iter_start as u32);
        invariant iter_done != 0 implies iter_start == 255u8 and total == 256u32;
        preserve by {
            have total == (iter_start as u32);
        }
    }
}
```

`click verify` reports `verification budget exhausted inside tactic solve`
for `__rust_mir_10 == 256`. On the exhausting pass the premises give
`total == iter_start as u32`, `iter_start <= 255`, the branch's
`!(iter_start < iter_end)` and `iter_end == 255`, so the member follows by
arithmetic.

The checked-in proof of `every_byte`, which keeps `total == iter_start + iter_done`,
verifies; this shape blocks rewriting it over `RangeInclusive`'s own
`iter.is_empty()`.

## Acceptance

- The member closes, or `solve` declines promptly naming what it lacks;
  premise spelling work stays proportional to the premises the goal can use.
- A regression with this proof, and a work bound on its premise-spelling
  operations.
