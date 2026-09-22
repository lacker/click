# The call-havoc retention's `local:` promise has no enforced boundary

P1. A deciding rule must require the evidence its conclusion depends on.
`call_havoc_keeps_cell` keeps a cell on the `local:` prefix alone, and the
premise that makes that sound is documented but not enforced in code.

## What was found

`call_havoc_keeps_cell` (`src/kernel/primitives/memory_state.rs:1355`)
retains a cell across a call havoc unconditionally when its block spelling
starts with `local:`. Its own doc concedes the soundness bridge: the
retention "is only sound while a checked write set can never be based in a
`local:` block, which holds because such a write set is the callee's owned
ranges resolved at the call site, and a `local:` range cannot be owned —
passing `&t` to a callee that owns `t[0..1]` is refused" — an argument
recorded in docs and in `docs/internals/resource-tracker.md`, and enforced
nowhere machine-checked.

The caller-side refusal it cites ("want of `owns local:t@0[0..1]`") plus
the alias hazard the rest of the hunt has promoted (proven-equal spellings)
mean the deciding rule's premise lives only in a remembered claim: a write
range whose base resolves (via proven-equal spelling facts or an
undecided-entry alias pairing) to a `local:` block reaches the havoc write
set, the `local:` disjunct keeps the cell anyway, and the caller's scalar
local keeps its pre-call value across a callee that wrote it.

Two enforcements to choose between at the fixer: (a) the `local:` arm
consults the fact context alias-equality against every `mutable_range`
base before keeping (the rule wants `pointers_proven_equal...)`)
consultation; or (b) the callee-side owned-range mint
(`src/kernel/functions.rs:17386`) *refuses* any owned range whose resolved
base is a `local:` block (or requires spelling re-resolution away from
`local:`), converting the doc comment's premise into a checked refusal at
production time.

Also present in the same rule: the fallback consult
`ranges_proven_disjoint_from_pointer` can fire on a `CResourceSeparate`
entry-partition fact (the presence-trusted class already filed in
`bugs/entry-partition-separation-facts-unrechecked.md`) — one fix shape
covers both.

## Intended regression

A kernel-level execution regression: a caller with a `local:t` scalar cell
and a callee whose contract owns a range resolved assumed-equal to
`&t[0]` (via symbolic argument equality) performs a write; the post-call
load must NOT keep reading the pre-call cell (dropped to unknown/refused),
and the *callee side* must refuse the `local:`-based owned range with a
named diagnostic.

## Acceptance

- [ ] Either the retention consults equality facts against the declared
      write set for `local:` blocks (retains only with the premise
      satisfied), or the owned-range mint refuses `local:`-based ranges
      outright, with the regression stating which.
- [ ] `scripts/check.sh` green.
