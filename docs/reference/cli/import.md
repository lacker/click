# `click import`

Compiler imports let a sidecar verify the C selected by a configured compiler
preprocessor. Click still parses and lowers the resulting C and independently
checks its proofs. This mode is explicit and separate from the existing bounded
source-bundle preprocessor.

```text
usage: click import lock <sidecar.click>
```

## Configure and lock an import

For `main.click`, create `main.click.import.json`. The configuration lists the
logical C sources named by the sidecar's `verifying` declarations, their compiler
inputs, and the output artifacts. For example:

```json
{
  "schema": 1,
  "target": "x86_64-linux-kernel",
  "compiler": "/usr/bin/gcc",
  "working_directory": ".",
  "environment": {
    "allow": {
      "PATH": "/usr/bin:/bin",
      "LC_ALL": "C",
      "SOURCE_DATE_EPOCH": "0"
    }
  },
  "sources": [
    {
      "logical_source": "main.c",
      "path": "main.c",
      "args": ["-DVARIANT=1", "-isystem", "configured"],
      "artifact": "main.i"
    }
  ]
}
```

The working directory is relative to the configuration file. Source and include
paths are interpreted in that working directory; artifact paths are relative
to the configuration file. Logical source paths identify translation units and
must match the sidecar, independently of the original header filenames used by
diagnostics.

Run `click import lock main.click` to create or explicitly refresh the configured
artifacts and `main.click.import.lock.json`. Then run `click verify main.click`.
The configuration's presence selects compiler mode for verification and its
associated proof tools. An invalid configuration or missing lock is an error;
it does not fall back to source-bundle mode.

Lock creation is source preparation, not proof verification. The C parser can
still reject an unsupported construct when a proof tool loads the prepared
translation unit. No C declarations, function bodies, storage, attributes, or
assembly are silently deleted to make an import pass.

## Validation and supported profile

Each load runs fresh preprocessing with controlled arguments and environment,
then compares the result and input identities with the existing lock. Changed
sources, used headers, toolchain inputs, configuration, or artifact bytes cannot
reuse an incompatible lock. Refreshing a lock is always a separate explicit
operation. A supplied digest alone never establishes a validated import.

The first profile uses GCC with `-x c`, `-std=gnu11`, `-m64`, `-funsigned-char`, and
`-nostdinc`. Configured include roots, forced includes, and ordered `-D` and `-U`
options select preprocessing inputs. Unsupported compiler options, response
files, plugins, and execution hooks are rejected. The compiler runs with a
cleared environment; only the configuration's supported variables are supplied.
Use explicit `SOURCE_DATE_EPOCH` when source depends on date/time macros.

Compiler invocation has output and time bounds, and failure or cancellation
stops its owned process group. Partial compiler output cannot become a
validated artifact. Dependencies come from the compiler's complete dependency
output, including configured system headers; source-map filenames are not a
substitute for that inventory.

The initial implementation snapshots the working directory, source directories,
and configured include roots before and after preprocessing. Keep them quiescent
during a load. Root/configuration/output paths with symlink components are
rejected; dependencies resolving outside the declared roots are also rejected.
Output parent directories must already exist. A project is limited to 512 MiB
and 200,000 entries in its input-root inventory, 64 MiB per artifact, 128 MiB of
combined artifacts, and 1 MiB each for its configuration and lock. Compiler
processes have a 30-second limit. Exceeding a limit is a diagnostic, never a
partial successful import.

Compiler imports initially reject incremental `--changed-since` requests and
do not use verification markers. Their proofs are checked through the same
engine used for ordinary verification, profiling, audit, and expansion.

## Locations and trust boundary

Structured compiler line markers preserve original filenames and line numbers
through parsing and lowering. Physical artifact positions remain available for
debugging. Textual markers do not provide full macro-expansion backtraces or
exact original columns inside expanded macros; diagnostics do not claim that
precision. A system-header marker does not suppress errors or omit code.

The compiler preprocessor is a trusted dependency for source selection.
Reproducing its invocation is not a formal proof that its preprocessing is
correct. It supplies neither executable C semantics nor proof authority to
Click: those remain in Click's frontend and independent kernel checker.

The captured Linux 6.8.12 rbtree translation unit is not yet supported by this
first profile. Its full header graph includes unsupported C forms, effectful
assembly, storage-producing exports, and additional compiler options. The
kernel capture records those gaps; it is not a passing verification fixture.

## Options and exit status

`--help` and `-h` show usage. `--` ends option parsing before a positional path.
A successful lock operation exits 0. Invalid configuration, missing inputs,
compiler failure, an exceeded bound, or an output-write failure exits nonzero
with a diagnostic. Ordinary verification never rewrites a lock or artifact.
