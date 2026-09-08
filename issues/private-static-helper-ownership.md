# Private static storage passed to pointer-taking helpers needs ownership

## Invariant

A public C wrapper should be verifiable when it passes its private static
object to a resource-contract helper. Its callers should not need to change
the C or gain source-level access to the private object. Initialization and
call boundaries must not duplicate ownership or silently strengthen a helper's
precondition by assuming its argument cannot alias static storage.

## Reproduction

Use two translation units and an ordinary public prototype:

```c
/* library.c */
struct counter { unsigned long value; };
static struct counter state = {7};
unsigned long bump(struct counter *p) { p->value += 1; return p->value; }
unsigned long next(void) { return bump(&state); }
/* client.c */
unsigned long next(void);
unsigned long twice(void) { next(); return next(); }
```

Give `bump` a loadable/consumes/produces contract for `p->value`, proving
`p->value == old(p->value) + 1u64` and `result == p->value`. The global struct
address parses with its correct nominal type, but `next` fails when the helper
requires ownership of the private field. Removing the helper's ownership
clauses instead fails its abstract pointer read with a missing view resource.
Adding a `mutable` footprint alone does not supply ownership.

This blocks the proposed unchanged pcg-c-basic global-state example at upstream
revision `bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3`:
<https://github.com/imneme/pcg-c-basic/tree/bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3>.
Its generator and reentrant seeding helpers can be proved with explicit field
resources; `pcg32_srandom` and `pcg32_random` pass private `pcg32_global` to
those helpers. The integer-narrowing prerequisite is separate from this gap.

## Acceptance criteria

The startup policy is now chosen: a distinguished, parameterless `main`
proof starts with the program's initialized static ownership and is not
published as a reusable call contract. This is not a module abstraction.
The remaining surface integration includes
[static resource proof bindings](static-resource-proof-bindings.md).
The private wrapper/PCG acceptance tests below are still outstanding.

- Choose and document a checked mechanism for private static ownership at
  public call boundaries; do not unconditionally mint ownership on every call.
- Prove the unchanged two-file pattern, repeated calls, and independent
  same-named statics in different translation units.
- Reject duplicated ownership, overlapping helper arguments, writes through
  const storage, and claims that a helper leaves aliased static state unchanged.
- Verify PCG's public seed/draw wrappers and a separate client checking its
  first two outputs and reset behavior, with pinned unchanged source hashes.
- Keep ordinary verification, expansion/reverification, and the full gate green.
