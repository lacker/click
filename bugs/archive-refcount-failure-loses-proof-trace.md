# Archived refcount failure loses its checked proof trace

Priority: P2.

Soundness: incomplete. On the preserved object-model recovery branch, the
original refcount proof fails at a pure comparison after verified C steps and
resource operations, but its opt-in trace reports that no checked path was
retained. This obstructs diagnosis of a known branch compatibility failure;
no false acceptance or corresponding failure on upstream is demonstrated.

## Reproduction

Recovery checkpoint `9d2c9dbc4`, with the original example C, resource definitions
and proofs unchanged:

```console
click verify --trace-proof refcount_pipeline examples/refcount/refcount.click
```

The selected proof reaches its `have amount < obj->refs by auto` after
`object_retain_many` and an `open(control(obj))`. It reports:

```text
`refcount_pipeline.contract` tactic 11
`auto` could not prove `amount < obj->refs`
proof trace unavailable: no checked path was retained for this failure
```

The checked prefix includes the branch, resource folds, modular call and open.
Its facts are needed to tell whether the count relation or its memory read was
lost. The rejection alone does not establish the semantic cause of the
refcount regression. A local transcript is
`target/refcount-after-frozen-unfold-trace.log`; the tracked example and command
above reproduce it without that build artifact.

## Acceptance

- Retain the checked prefix and the facts actually added to its environment at
  this pure-step refusal, using the existing opt-in trace.
- Preserve the original C, claims and proof; do not raise search limits or add
  arbitrary diagnostic facts to make the comparison succeed.
- Reduce the recording/retention failure and check that the trace survives
  failure after a modular call and resource open, with the relevant branch
  retained.
- Then use that evidence to investigate the refcount compatibility regression.

## Shared minimal reproduction

The same defect also reproduces on upstream `804be33ee`; it is not specific to
native object inputs. Use this valid C:

```c filename=f.c
int helper(void) { return 1; }
int f(void) { int x; x = helper(); return x; }
```

```click
verifying "f.c";
int32 helper() { ensures result == 1; } by { execute(); simp(); }
int32 f() { ensures result == 1; } by {
    step();
    step();
    have x == 2 by auto;
    execute();
    simp();
}
```

The false `have` must fail. Under `with_proof_trace("f", ...)`, however,
`error.trace_context_report()` is `None`, despite the two checked steps and the
helper's `x == 1` result. The early auto-miss return in `source_have_error`
constructs a fresh error without the existing diagnostic attachment used by
its other error paths. Preserve that exact checked predecessor and the existing
failure message; failed smart candidates must not become trace facts.

## Checked repair candidate

The source auto-miss now attaches its checked predecessor's existing diagnostic
provider, as the other source-have refusals do. The original error message is
unchanged. A regression checks the helper-call prefix and excludes publication
of the failed claim. That regression and the existing call-trace control pass
on both trees; all 73 active diagnostic tests pass upstream (nine ignored).

The original refcount trace now records initialization, folds and the retain
call, including a post-call read equal to `1 + amount`. The functional
comparison still fails. Investigate its exact goal read and state transport;
this trace repair is not a refcount proof repair. Keep this file until the
shared diagnostic fix lands upstream.
