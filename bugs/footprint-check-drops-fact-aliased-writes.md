# Footprint refusals drop writes spelled through fact-proven aliases

P1. Every write must be checked against the declared mutable footprint; a
check that treats "unresolved spelling" as "cannot write real storage" is
unsound once an assumed equality proves the spelling names real storage.

## What was found

`src/surface/checking/segments.rs:81` (`is_preexisting_write_pointer`)
filters the write-pointer sweep and the effect-summary sweep before the
"write outside the mutable footprint" refusals. A write pointer whose block
is `Symbolic(_)` or `Heap(_)` is kept only when `has_block` answers true or
`is_live_heap_address` answers true *with an empty fact context*
(`&PureFactContext::new()` at lines 88-90).
`heap_allocation_may_contain_pointer` answers the cross-spelling route only
through assumed pointer equalities, so a write through a pointer the
assumptions prove alias to a preexisting allocation or global is silently
dropped from both sweeps: the write escapes the footprint refusal instead of
being reported as outside the mutable footprint.

`src/kernel/api.rs:116` (`c_memory_holds_live_heap_allocation_at`) documents
itself as "assumption-free", but that is precisely what makes the surface
gate blind at this boundary — the write pointer's real identity is only
available in the path's fact context, which the call does not pass.

## Intended regression

A surface-level test where the effect's write range base is a `Symbolic`
pointer with an assumed `PointerEqual` alias to a preexisting object outside
the declared mutable footprint. The refusal sweep must use the path's fact
context at the deciding sweep, not the empty context, and the aliased write
must be reported or refused instead of escaping the sweep.

## Acceptance

- [ ] The write-pointer and effect-summary sweep run with the fact context
      that decides aliasing, or every dropped pointer is conservatively
      refused elsewhere at the same decision point.
- [ ] `scripts/check.sh` green.
