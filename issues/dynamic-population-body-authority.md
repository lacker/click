# Represent dynamic population bodies without stale ownership

Ordinary resource populations now keep an invariant-bearing body active across
opaque calls when that body's resource footprint is determined entirely by
the resource arguments. This covers bodies such as `owns object(obj)` even
when their pure facts depend on mutable C memory.

A body whose owned footprint itself depends on a load, guard, or recursive
path still needs a stronger representation. Naively refreshing such a body at
the post-call snapshot can leave its old range beside its new range, or leave
both a folded resource and independently usable overlapping ownership. The
owned-vector regressions demonstrated both failure modes.

## Regression

Use a wrapper whose body owns a range selected by mutable metadata. Produce
the wrapper through an opaque call, change that metadata through its contract,
then use and finally consume the wrapper. Replay and independent certification
must agree about which pre-state body was retired and which post-state body is
active.

Split guarded and recursive bodies into separate issues if they require
different authority representations.

## Acceptance criteria

- A transition retires the exact pre-state footprint before activating the
  exact post-state footprint.
- The folded unit and active body are treated as one representation; generic
  expansion, transfer, and allocation inspection cannot duplicate ownership.
- No stale range survives a metadata-changing call.
- Existing owned-vector, owned-box, borrowed-slice, and stable-body regressions
  remain green without changing their C.
