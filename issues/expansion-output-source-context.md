# Preserve source context when expansion writes to another directory

P2: the documented `--output /tmp/expanded.click` workflow emits an artifact
that cannot be verified at its output path. Reproduced at `3ad0d2e1`.

## Violated invariant

An expansion advertised as a verified output artifact must retain the C input
and import context against which its proof was checked. Moving a sidecar must
not silently change what its relative `verifying` declarations refer to.

`src/bin/click-expand.rs` loads inputs relative to the original sidecar,
checks the rewrite against those in-memory inputs, then writes it to the
requested output path. `verifying` declarations are preserved unchanged.
`src/cli.rs::read_c_inputs` resolves those declarations and any adjacent import
manifest relative to the new path when the user verifies the emitted file.
The documentation explicitly demonstrates output into `/tmp` and instructs
users to verify the exact output afterward.

## Small reproduction

Create sibling directories `source/` and `out/`. In `source/identity.c`:

```c
int identity(int x) { return x; }
```

In `source/identity.click`:

```click
verifying "identity.c";
int identity(int x) {
    ensures result == x by { execute(); simp(); }
}
```

Run:

```sh
click verify source/identity.click
click expand --claim identity.ensures_0 \
    --output out/identity.click source/identity.click
click verify out/identity.click
```

Verification of the original and expansion both exit 0. The emitted file
still begins `verifying "identity.c";`. Verification of that exact artifact
exits 1 with `failed to read 'identity.c': No such file or directory`.
An unrelated file with the same name in `out/` would instead be selected as
the C input. Prepared imports have a related identity requirement because
their manifest is located by the sidecar filename.

## Acceptance criteria

- Define how an emitted artifact retains its original source and import
  context. Rebase references or carry the required context, or reject an
  output destination that cannot preserve it before writing the artifact.
- Reconcile this behavior with the promise to preserve unselected source
  text and document the supported workflow without requiring a manual
  dependency-copy recipe.
- Add CLI coverage for output in the same directory, another directory,
  a destination with a conflicting C filename, and a prepared-import
  sidecar renamed or relocated by `--output`.
- Verify the emitted artifact through its actual output-path loading rules;
  failures must leave the requested artifact unwritten. `scripts/check.sh`
  passes.
