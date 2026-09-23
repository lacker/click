# Frozen fork/join example

This synthetic C11/POSIX program is verified with the project's
`x86_64-linux-userspace` target and explicit `modeled-pthread` runtime. The
sidecar proves `fill_range` and all three `fill_parallel` outcomes: creation
fails before either child runs, creation of the second child fails after the
first succeeds, or both children succeed. The output buffer remains owned by
the caller at return. The C source is unchanged from the frozen selection and
its SHA-256 is pinned in `tests/examples.rs`.

The runtime assumption covers the selected modeled create/join operations;
this proof does not validate a native Linux or macOS pthread implementation.
The [profile record](../../design/concurrency-probes/README.md) documents the
source, declarations, assumption, and remaining native binding work.
