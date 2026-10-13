# Multifile Registry

A synthetic integration example for shared counters named `a`, `b`, and `z`.
It combines ordinary C module boundaries with several supported initialization
and preprocessing forms. It is not imported third-party code.

| File | Role |
| --- | --- |
| `registry.h` | Struct, extern declarations, prototypes, guards, macros |
| `client.h` | Includes the shared header along a second path |
| `data.c` | Data-only translation unit with inferred struct and const scalar arrays |
| `alpha.c` | Updates counter a; private scalar and persistent multidimensional local array |
| `beta.c` | Updates counter b; same-spelled private scalar and persistent local struct array |
| `driver.c` | Calls alpha twice and beta once, then observes both private totals |
| `registry.click` | Contracts and proofs for all functions |

The sidecar deliberately lists the driver before the definitions. Both clients
reach the shared header twice, exercising include guards. The source also uses
a function-like macro, conditional compilation, standard integer spellings,
inferred outer bounds, short-row zero-fill, and const storage.

Starting with the declared initial state, the driver proves:

- Alpha returns 2 and then 4, demonstrating persistent local state.
- Beta returns 102, while the two private `calls` objects end at 2 and 101.
- Shared values end at 12, 21, and 99; all three name fields remain unchanged.
- The combined driver result is 214, including zero-filled and explicit entries
  of the const lookup table.

Helper contracts describe updates relative to entry values with `old()` and
authorize their write footprints. The driver proof records intermediate call
results with small explicit steps before closing the final arithmetic claim.
Each call initializer lowers to a call step followed by its local assignment.

C translation: the initial driver expression called both read-only getters
inside one sum. Click currently rejects multiple unsequenced calls in an
expression, so `driver.c` explicitly stores their results in local snapshots.
The getters have no side effects, so this sequencing preserves behavior.
This example does not demonstrate support for the original unsequenced form.

Run from the repository root:

```sh
cargo run --bin click -- verify examples/multifile-registry/registry.click
```

The project does not verify yet. `click verify` and the examples gate agree:
both stop at `registry_run`'s entry, which cannot evaluate
`owns beta::record_beta::batches[0].value` (an owned field path into
another module's function-local static struct array has no known pointee
type), and past that point the cross-file caller needs static-state caller
transport (`issues/static-state-caller-transport.md`). The examples gate
quarantines the directory until then; `CLICK_EXAMPLE=multifile-registry` runs
it.
