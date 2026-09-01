# Account for memory and call writes to the termination measure

Found by the 2026-09-01 kernel audit at cb034b21.

`c_verified_function_termination_rules` (`src/kernel/termination.rs:854`)
checks a surface `CFunctionTerminationPlan` purely syntactically over
`Assign` statements. In `loop_paths` (`termination.rs:732-779`) `Store` and
`TypedStore` are no-ops (`:738-743`) and `Call` and `CallAssign` to another
target are no-ops (`:758-762`); `recursion_paths` does the same (`Store` at
`:619-624`, `Call` at `:664-687`, which checks only the recursive argument
shape). Neither consults aliasing, callee write effects, or symbolic
execution. A write to the measure's stack cell through an escaped address,
directly (`*p = 10` after `p = &i`) or through a helper call receiving
`&measure`, is invisible to the ranking, although the kernel's own execution
model treats such a store as writing the local (`address_escaped_scalar_locals`,
`src/kernel/loops.rs:1734`; mdtest `loop_rejects_stale_address_escaped_local`).
Surface plan construction (`src/surface/verification.rs:1440-1579`) validates
only that the measure is a bare variable name (`termination_measure_name`,
`:1440-1450`) and, for function-level `decreases` only, that it is an int32
parameter (`:1489-1494`); loop measures get no type check at the surface or
in `check_loops` (`termination.rs:781-829`). The terminating-callee closure
(`termination.rs:1015-1032`) does not help: a terminating helper can still
reset the measure. The false rule is consumed at
`src/surface/verification.rs:1219-1235` and surfaced by
`function_termination_is_verified`.

Partial-correctness rules are unaffected; only termination evidence is wrong.

## Violated invariant

A `CVerifiedFunctionTerminationRule` may be constructed only when the measure
provably strictly decreases and stays well-founded on every back edge and
recursive edge, accounting for every way the body can change the measure's
storage, including stores through pointers and callee effects.

## Intended regression

```c
int32 spin(int32 n) {
    int32 i; int32* p; i = 10; p = &i;
    while (i > 0) { i = i - 1; *p = 10; }
    return 0;
}
```

`spin` never terminates (`i` is reset to 10 every iteration). With a sidecar
that gets partial correctness through the loop and names `decreases i`, today
`function_termination_is_verified("spin")` returns true. It must instead fail
with a diagnostic naming the memory write to the measure. Second regression:

```c
int32 f(int32 n) { int32* p; p = &n; if (n > 0) { *p = 1000; f(n - 1); } return 0; }
```

with `decreases n` must be rejected. Third: the same shapes with the reset
performed by a helper `reset(int32* q)` that stores through `q`.

## Acceptance criteria

- Ranking rejects (or accounts for) any `Store`/`TypedStore` whose target may
  alias the measure's cell, and any call that receives the measure's address
  or whose contract's mutable footprint may cover it, in both `loop_paths` and
  `recursion_paths`.
- A measure whose address escapes anywhere in the function is rejected unless
  the escape is proved harmless.
- Kernel unit tests for the loop, recursion, and helper-call forms; negative
  mdtests for each; the existing happy-path termination tests in
  `src/surface/tests/project_tests.rs` and `loop_tests.rs` still pass.
- `scripts/check.sh` passes.

Related: [termination-ranking-coverage.md](termination-ranking-coverage.md)
tracks the loop shapes the ranking cannot express.
