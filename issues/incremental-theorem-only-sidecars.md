# Verify theorem-only sidecars during incremental full rebuilds

P1: `click verify --changed-since` accepts an unproved false theorem.
Reproduced at `3ad0d2e1` without any baseline verification marker.

## Violated invariant

Incremental verification may reuse only attested proof results. A required
full rebuild must verify every selected kind of declaration, even when the
sidecar contains no C function contracts.

`verify_changed` in `src/bin/click-verify.rs` computes its selection with
`c0_function_names`, then immediately continues when `selected.is_empty()`.
This happens even when `full_rebuild` is true because the baseline is
unattested or shared theorem definitions changed. The resulting success
message counts the sidecar as unchanged without checking its theorems.

## Small reproduction

In a fresh temporary Git repository, create and commit `proof.click`:

```click
theorem wrong() {
    ensures 1 == 2 by { normalize(); }
}
```

Run:

```sh
click verify proof.click
click verify --changed-since HEAD proof.click
```

The ordinary command exits 1 because `normalize` cannot prove the false
claim. The incremental command exits 0 and prints:

```text
mode: full rebuild
selected (0): (none)
reused (0): (none)
because: baseline commit ... has no valid full-verification marker ...
incremental verification completed: 0 sidecars verified, 1 unchanged sidecars skipped
```

No malicious cache modification, C program, or smart tactic is needed.

## Acceptance criteria

- Execute a full rebuild whenever required, independently of the C function
  count. Represent or conservatively verify non-C proof units in incremental
  selection.
- Add regressions for an unattested false theorem-only sidecar and for a
  previously verified theorem-only sidecar whose theorem is changed to a
  false claim. Both incremental runs must fail.
- A valid theorem-only sidecar must verify and support sound reuse; reports
  must distinguish an actually unchanged sidecar from an empty C selection.
- Preserve normal C function dependency selection and `--explain` dry-run
  behavior. `scripts/check.sh` passes.
