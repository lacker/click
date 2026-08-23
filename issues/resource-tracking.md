# Resource tracking across execution transitions

## Invariant to audit

When the execution frontier advances through a C statement, its successor
`CState` must contain exactly the resources still valid after that
statement's transfers, consumption, production, mutation, and lifetime
effects.

For a verified call, the transition is conceptually:

```text
successor resources
    = valid caller frame
    - resources transferred to or consumed by the callee
    + resources produced by the callee
```

Views require an explicit lifetime rule. Click already documents this rule:

- a `views` requirement borrowed from caller ownership is scoped to that
  call and does not create a persistent caller view on return;
- a view already present in the caller is persistent and blocks retirement
  of memory it may reference; and
- a view proved separate from retired memory survives.

The resource engine must enforce that rule identically for direct mutation,
direct `free`, and opaque verified calls. The proof object should retain the
checked successor state, not implement a second resource-transition model.

## State-transition architecture

An execution-frontier `Proof` contains an `ExecutionProofState`, whose
semantic state is a `CState`. `CState` contains locals, symbolic memory, a
`ResourceContext`, and counted resource populations. `step()` checks its
selected premises, asks the kernel for a certified statement successor, and
replaces the focused frontier with the returned state.

For an opaque verified call, the kernel separates resources transferred to
the callee from the caller frame, evaluates the callee's returned resources,
applies allocation-lifetime effects, and installs the resulting memory and
resource context in the caller's next state. A lifetime transition may reject
the successor when the caller frame still contains a persistent resource that
could refer to retired memory.

`ResourceContext` is an immutable indexed resource snapshot. This is the
authoritative resource component of the current C state; proof facts about
resources are observations of that state, not a second ownership store. A
resource-tracking fix must update or reject this context through the shared
kernel transition rather than editing proof-object bookkeeping after the
fact.

## Current reproduction

`examples/owned-vector` is quarantined. In the
`owner->len == owner->cap` branch of `allocated_vector_push.contract`, the
proof begins with:

```click
observe(allocated_vector(owner));
```

`observe` is deliberately non-consuming: it retains the owned composite and
records persistent immediate child views of the owner fields, allocation
token, and old data range. A later `step()` applies the verified
`vector_grow(owner)` rule. On its success path, `vector_grow` allocates new
data, copies the elements, updates the owner, and frees the old data.

The caller frame still contains the persistent observed view of that retired
range, so the transition correctly refuses to create an invalid successor:

```text
resource would remain usable after its allocation is freed:
views owner[(...old data base...)..(... + load(owner->cap))]
```

This is a prompt safety failure, not a use-after-free being accepted. It
reproduces before the final proof-object migration and is not canonicalization
fallout.

## Existing scoped mechanism

The earlier `borrowed-resource-lifetime-at-free` issue chose and documented
the persistent-view semantics above. The repository already has regressions
that:

- allow a call-scoped borrow to end before `free`;
- reject `free` when an independently persistent composite view remains; and
- preserve a view proved separate from the freed allocation.

Proof scripts also have a scoped resource operation:

```click
open(resource) {
    // immediate shared body is available here
    // proof and execution steps may run here
}
// the exposed body is closed here
```

By contrast, `observe(resource)` records non-consuming child views without a
matching close operation. Therefore the owned-vector failure may be a proof
scope error rather than an incorrect kernel transition: the proof asks for
persistent observations and then tries to cross a call that invalidates one.

The first implementation task is to express the owned-vector preparation
with `open(allocated_vector(owner)) { ... }`, or with an explicit
unfold/fold scope, so the temporary resource exposure closes before the
consuming `vector_grow` call. Do not weaken the verifier by automatically
deleting persistent views merely to make this proof pass.

If the existing scoped operations cannot express that proof, reduce the
missing simple resource step. A new operation must have explicit checked
semantics—for example, closing one named observation projection—not infer
revocation from a later mutation or grant smart tactics authority unavailable
to simple replay.

## Support-aware representation checkpoint

Returned cores are now stored as derived views supported by the exact owned
resource generation that produced them. `ResourceContext` maintains the
reverse support index, so consuming an authority retires only its projections;
an identical explicit persistent view remains independent and still blocks a
conflicting lifetime transition. Certified owned expansions are cached on the
same support record so later inspection does not mint a different symbolic
load identity for the same generation. Normalization and branch joins preserve
only support metadata common to their surviving ownership.

The deterministic regression grows the unrelated frame from 16 through 4,096
facts while holding eight projections fixed. Retirement visits exactly those
eight projections at every size. The ordinary heap regressions still reject an
explicit persistent view at `free` and preserve a proved-separate view.

The focused scoped-open regression now passes. Opaque allocation lifetime
effects lower provisional ensures first, split only when returned and consumed
allocation identities remain undecided, and retain one checked successor per
identity case. The checked `Proof` statement operation can retain that binary
partition. The remaining legacy grouped-replay adapter still rejects the same
ordinary `step()` because it requires exactly one successor; completing that
handoff belongs to `replay-smell.md`, not to a new resource operation or surface
tactic. The generated identity condition is snapshot-qualified, and
whole-function replay lowers it separately for each concrete outcome instead
of reusing one branch's fresh kernel variables.

The returned dynamic-range association is now reduced and covered separately.
Opaque lifetime checking first classifies returned allocation continuity by
base and size, then checks only the preserved caller frame for resources that
would survive retirement. Projections of the returned composite describe the
successor allocation and are never mistaken for persistent caller views. The
focused regression uses a returned allocation and owned range whose size is a
mutable field; it fails on the old kernel with the same stale returned `owns`
diagnostic and passes with the corrected transition.

Applying the scoped proof repair to `owned-vector` and selecting the existing
multi-successor-aware explicit statement operation advances beyond that runtime
error. A current 30-second profile then spends 22.821 seconds lowering
provisional `vector_push` ensures and performs 98,586 range-membership offset
equality queries before timing out. This is a distinct verifier-core scaling
invariant with a different likely fix, so its reduction remains in
`owned-vector-provisional-ensure-scaling.md`. The incomplete owned-vector proof
edit remains out of this green resource-kernel checkpoint.

## Remaining roadmap

1. Complete the ordinary statement-step handoff in `replay-smell.md`, so a
   plain `step()` retains the kernel-certified successor partition through
   `Proof` without a parallel exactly-one replay rule. Do not add resource
   semantics or require different surface syntax for this adapter gap.
2. Reduce and fix the provisional-ensure query curve in
   `owned-vector-provisional-ensure-scaling.md`. Judge it with deterministic
   work over several context sizes, not only the owned-vector wall clock.
3. Land the scoped `open(allocated_vector(owner))` proof repair, finish the
   unchanged owned-vector proof, remove its quarantine, and run the full gate.
4. Close this issue only after the focused lifetime regressions, resource
   scaling regression, and owned-vector end-to-end case are all green. File a
   new issue only if that completed path exposes another independent invariant.

## Intended regressions

### Scoped preparation before mutation

Open an owned composite, execute the read-only steps needed to select a
branch, close the scope, then pass the retained owned composite through a
verified call that may replace and retire an allocation. The success path
must advance with no stale temporary views.

### Persistent views still block retirement

Retain an explicitly persistent direct and composite view of an allocation
and confirm that direct `free` and an opaque retiring call both reject the
transition locally. Do not silently drop these views.

### Independent resources survive

Keep a view of unrelated live memory across the same transition and assert
that it remains in the successor `ResourceContext`.

### Path-sensitive lifetime effects

Use a call with success and failure outcomes like `vector_grow`: the success
path retires the old allocation after temporary scopes are closed, while the
failure path retains the old allocation and its valid persistent caller
resources.

### Direct and opaque transition parity

Exercise equivalent lifetime changes through direct `free` and a verified
function rule. Both paths must apply the documented persistent/scoped view
law and emit consistent lifetime facts.

### Deterministic scaling

Build resource frames with several numbers of unrelated facts and measure
deterministic work for the selected transition. Resource updates must use the
persistent indexes and output-sized deltas rather than clone or scan unrelated
project-wide state.

The unchanged owned-vector C source is the end-to-end regression. Its Click
proof may change to use the correct explicit resource scope; its contract and
proof intent must not be weakened.

## Acceptance criteria

- The owned-vector failure is first tested with the existing `open` or
  unfold/fold resource scope rather than an automatic persistent-view drop.
- Advancing an execution frontier uses one checked successor
  `ResourceContext` for resource transfers, consumption, production,
  mutation, and allocation lifetime effects.
- Call-scoped borrows end at return, persistent views block overlapping
  retirement, and proven-independent views survive.
- Direct statements and opaque verified calls implement the same lifetime
  law.
- Success and failure outcomes retain their distinct resource and allocation
  states.
- Any missing resource operation is added as a bounded simple certificate
  step before smart tactics are taught to use it.
- Resource-transition scaling satisfies the documented
  linear-up-to-indexing complexity contract.
- `allocated_vector_push.contract` advances past the current runtime error
  without editing its C implementation or weakening its contract.
- If a later independent owned-vector failure appears, it receives its own
  focused issue rather than being folded into this one.
- `examples/owned-vector` leaves quarantine and `scripts/check.sh` is green.
- This file and its Open-list line are deleted when the proof repair or
  missing simple operation, regressions, and documentation land.
