# Split the nested callback expansion regression into bounded cases

## Invariant

Each unit regression must stay below the default nextest ten-second slow-test
threshold without increasing time budgets or dropping certificate checks.

## Reproduction

Run `scripts/check.sh`. The existing
`surface::tests::expansion_tests::nested_callback_status_cases_expand_at_every_theorem_site`
test aggregates many expansion/reverification operations. It took 28.8 seconds
in the qualified-static ownership integration gate and 30.4 seconds in the
mutating-private-state gate. This predates the mutating wrapper changes.

## Acceptance criteria

- Split the cases into independently bounded tests, preserving ordinary
  verification and expansion/reverification for every theorem site.
- If an individual case is still slow, reduce and repair its verifier issue
  rather than increasing the timeout or deleting coverage.
- Run the focused cases and the full gate without this test reporting slow.
