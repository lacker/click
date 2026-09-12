# Attest every verified dependency before reusing an incremental baseline

P1: incremental verification can report success for a false C contract.
Reproduced at `3ad0d2e1` with the ordinary `click` binary.

## Violated invariant

A full-verification marker must attest the exact sidecar and complete C input
bundle verified at the named commit. Uncommitted changes to an included header
must prevent that commit from being recorded as verified.

`record_full_verification` in `src/bin/click-verify.rs` builds its `tracked`
list from the sidecar and `verifying_source_paths`. That list contains only
directly declared sources. `read_verifying_sources` in `src/cli.rs` also loads
transitive local headers, so the verifier can prove a modified program while
the marker's Git cleanliness checks examine a smaller set of files.

## Small reproduction

Create these three files in a fresh temporary Git repository:

```c
/* cap.h */
#define CAP 2
```

```c
/* probe.c */
#include "cap.h"
int probe(void) { return CAP; }
```

```click
// probe.click
verifying "probe.c";
int probe() {
    ensures result == 1;
} by { execute(); simp(); }
```

Commit all three files. Use the same verifier executable and environment
throughout this sequence:

1. `click verify probe.click` fails: the result is 2, not 1.
2. Change only `cap.h` to `#define CAP 1`, without committing it.
3. `click verify probe.click` succeeds and incorrectly records a marker for
   the unchanged `HEAD` commit.
4. Run `git restore cap.h` to restore the false contract's input.
5. `click verify probe.click` fails again.
6. `click verify --changed-since HEAD probe.click` exits 0 and prints
   `selected (0): (none)`, `reused (1): probe`, and
   `0 sidecars verified, 1 unchanged sidecars skipped`.

The semantic comparison correctly sees that the restored files equal `HEAD`;
the unsound step is attesting `HEAD` from different header contents. This is
independent of compiler-prepared imports, which currently reject incremental
verification, and of the existing general header-support issues.

## Acceptance criteria

- Derive attestation dependencies from the complete verified input snapshot,
  including transitively included headers, and ensure that snapshot matches
  the commit being attested.
- Add CLI regressions covering dirty direct and transitive headers, including
  staged header changes. No such run may create a usable marker for a
  different program.
- The final incremental command above must fail through full verification;
  legitimate clean baselines must still reuse unchanged results.
- Retain dependency provenance through attestation instead of independently
  reconstructing a narrower list of source files. `scripts/check.sh` passes.
