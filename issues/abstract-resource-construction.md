# Let verified C construct the first unit of a declared resource

Found by the 2026-09-01 kernel audit at cb034b21.

Declared (abstract) resources can be assumed, transferred, returned, or
consumed, but `docs/concepts/resources.md:238` states they "have no local
fold or construction rule: a contract may assume, transfer, return, or
consume an abstract unit, but verified code cannot establish its first unit."
A factory function (one that opens a descriptor and should produce
`open_fd(fd)`, or installs a capability) cannot be proved to create the
capability; only composite resources with bodies can be folded.

## Violated invariant

A resource that a project declares should have a documented, checkable way
to come into existence in verified code, so that the function that creates
the underlying state is the one that mints the resource, and nothing else
can.

## Intended regression

Mdtest: an `abstract resource open_fd(fd: int32);` with a designated
constructor function `int32 open_thing(void)` whose sidecar declares
`produces open_fd(result)` (Click has no conditional `produces ... when`
clause today; add one as part of this issue and say so in the acceptance
criteria, or keep the constructor contract unconditional) and whose proof
establishes it
through an explicit construction step tied to the C effect that creates the
state (or through a designated axiom recorded on the resource). A negative
mdtest shows a second function cannot mint `open_fd` without the designation.

## Acceptance criteria

- Surface Click has a form to designate which functions may construct a
  declared resource (or an explicit `axiom` form that names the resource and
  is reported by `click verify` as a project assumption).
- The kernel records the construction as a checked zero-source event in the
  proof object, distinct from contract transfer.
- The tests above pass; `scripts/check.sh` passes.

Related: [resource-algebra-extensions.md](resource-algebra-extensions.md).
