# Update resource-pattern counts across contracts

`count(resource(pattern))` can aggregate the resources held at one proof
point, but a wildcard observation is not yet maintained modularly when an
opaque call produces or consumes a matching exact resource.

For example, a contract transition from `available(object)` to
`pool_object(pool, object)` must increase
`count(pool_object(pool, _))` by one. The inverse transition must decrease it.
This is a logical resource transition, not a heuristic inference.

## Regression

Use a small pool struct with only a `checked_out` field, one exact object
identity, and a validity predicate equating the field to
`count(pool_object(pool, _))`. Prove one checkout and one return through opaque
contracts. Include two independent pool identities so an update to one cannot
change the other's observation.

## Acceptance criteria

- Exact produced and consumed resources update every matching active pattern.
- Nonmatching resource names and arguments are unchanged.
- Zero, one, and multiple exact identities are covered.
- Search and certificate replay use the same aggregate count transition.
- Direct verification, profiling, expansion, and audit remain prompt and
  agree.
