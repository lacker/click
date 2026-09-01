# Extend the resource algebra: fractions, persistent tokens, mutual recursion, symbolic coefficients

Found by the 2026-09-01 kernel audit at cb034b21. `docs/internals/roadmap.md:133-137`
and `docs/concepts/resources.md:589-599` already list most of these as
future work; this issue records the concrete rejection sites and a
regression for each so any one can be picked up independently.

- **Fractional and persistent read permissions.** Shared read-only structures
  (several readers of one buffer across call boundaries) need exact-transfer
  choreography in every contract. Not implemented (`resources.md:589-599`).
- **Mutual recursion between composites.** Only guarded direct self-recursion
  is permitted; a cycle spanning two composite names is rejected
  (`src/surface/validation/definition_validation.rs:1614-1675`
  `reject_composite_resource_cycles`; `resources.md:437`).
- **Symbolic coefficients.** `owns amount of p[0..1]`, symbolic allocation
  counts, and symbolic quantities of recursive composites are rejected
  (`src/surface/validation/type_validation.rs:687-705`; `resources.md:263-265`).
- **Automatic fold and unfold.** `auto` never selects resource unfold or
  fold, so every composite layer a proof needs must be named explicitly
  (`resources.md:589-599`).

## Violated invariant

The resource language should express the ownership disciplines real C code
uses: shared read access, mutually referencing ownership families, runtime
counts of memory-backed units, and routine folding that a proof author should
not have to spell out.

## Intended regression

One mdtest per bullet: two callees each `views` half a buffer concurrently
via fractions and the caller reassembles full ownership; a parent/child pair
of composite resources referencing each other; `consumes n of slot(p)` with
symbolic `n` over memory-backed units; a proof closed by `auto` that needs
one unfold of a composite.

## Acceptance criteria

- Each bullet lands with its kernel rule, surface form, and documentation,
  or is split into its own issue when work starts.
- Separation, containment, and population reasoning remain kernel-checked
  against the exact definition for the new forms.
- `scripts/check.sh` passes.

Related: [abstract-resource-construction.md](abstract-resource-construction.md);
[arena-resource-ownership.md](arena-resource-ownership.md).
