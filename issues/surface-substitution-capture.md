# Make surface proposition substitution capture-avoiding

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced end to end with
`click verify` (exit 0) on a three-function project whose caller returns 0
under `ensures result >= 2`.

`substitute_click_proposition` and `substitute_contract_expression`
(`src/surface/lowering/contract_substitution.rs`) handle every binder
(ForAll `:273`, Exists `:282`, RangeAll `:291`, RangeAny `:306`, RangeFold
`~:1500`, Let `~:1520`) only by removing the substitution whose key equals the
binder name. They never check whether a substituted value mentions the binder
and never rename the binder, so substituting `n := i` into
`forall (i: int32) { ... n >= i }` yields `forall (i) { ... i >= i }`.

The exploitable consumer is composite-resource fold and unfold. Kernel
composite tokens are abstract (`CResource::Token { name, arguments }`, no
attached facts); a body's facts are instantiated only by
`resource_argument_substitutions` plus `substitute_click_proposition` at fold
(`src/surface/proof/resources.rs:2385`) and unfold (`resources.rs:2070`). The
producer and consumer spell the argument differently, so a body binder that
collides with the producer's argument name makes the producer prove a
captured, trivially true instance while the consumer assumes the correct one.
The kernel's capture-safe population-invariant check
(`src/kernel/functions.rs:2537` via
`evaluate_resource_population_fact_propositions`) runs only when
`definition_has_population_wide_body` holds (`functions.rs:1952`: non-recursive,
no `if` condition, snapshot-independent `contains`), so any guarded body skips
it. Pure-theorem induction is not affected: it re-instantiates through the
kernel value environment and checks against `prove_forall_int32_application`.

## Violated invariant

Substituting actuals for formals in a surface proposition must be
capture-avoiding: a free variable inside a substituted value must never become
bound by a binder in the target proposition. The instantiated body facts a
composite resource carries at fold must be the same propositions the consumer
assumes at unfold.

## Intended regression

```c
int32 make(int32* p, int32 i) { return 0; }
int32 take(int32* p, int32 n) { return n; }
int32 pipeline(int32* p, int32 i) { int32 made; int32 r; made = make(p, i); r = take(p, i); return r; }
```

```click
resource bound(p: int32*, n: int32) {
    if p != 0 { owns p[0..1]; fact forall (i: int32) { 0 <= i and i < 3 implies n >= i }; }
}
verifying "make.c"; verifying "take.c"; verifying "pipeline.c";
int32 make(int32* p, int32 i) {
    requires p != 0; consumes p[0..1]; produces bound(p, i); ensures result == 0;
} by { fold(bound(p, i)); execute(); simp(); }
int32 take(int32* p, int32 n) {
    requires p != 0; consumes bound(p, n); produces p[0..1];
    ensures result == n; ensures result >= 2;
} by { unfold(bound(p, n)); execute();
       have 0 <= 2 and 2 < 3 by { simp(); }
       have n >= 2 by { instantiate(forall (i: int32) { 0 <= i and i < 3 implies n >= i }, 2) using { 0 <= 2 and 2 < 3; } assumption(); }
       simp(); }
int32 pipeline(int32* p, int32 i) {
    requires p != 0; requires i == 0; consumes p[0..1]; produces p[0..1];
    ensures result >= 2;
} by { execute(); simp(); }
```

Today all three certify. After the fix `make`'s `fold` must fail with the same
"requires an exact body fact" diagnostic the controls produce today (renaming
the binder to `k`, or the parameter to `m`, each makes `fold` fail).

## Acceptance criteria

- Every binder arm in `contract_substitution.rs` alpha-renames the binder to a
  name fresh with respect to the substitution values before descending, or
  the substitution rejects the collision with a positioned error.
- A surface unit test substitutes a value mentioning `i` into a `forall (i)`
  body and asserts the result binds a different name.
- The kernel independently checks the folded facts of every composite body,
  not only population-wide bodies, so a future surface regression here cannot
  reach a certified verdict; at minimum `definition_has_population_wide_body`
  no longer gates the check for guarded bodies.
- Negative mdtest for the regression above; a positive mdtest with a renamed
  binder verifies unchanged.
- `scripts/check.sh` passes.

Related: [kernel-binder-hygiene.md](kernel-binder-hygiene.md).
