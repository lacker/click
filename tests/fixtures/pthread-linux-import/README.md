# Frozen pthread source, prepared by Linux GCC

`main.c` is byte-identical to `examples/concurrency-fork-join/fork_join.c`.
Ubuntu 24.04's `/usr/bin/gcc` prepared `main.i` and the version-2 import lock
using its installed GCC 13 and glibc 2.39 headers. The lock records the
compiler, ABI observations, opened headers, and source profile. The normal
Mac unit test relocates this fixture and loads it without that toolchain.

This fixture pins the current full-header parser frontier. It does not select
the modeled pthread runtime or validate the native pthread implementation.
Refresh the config, lock, and artifact together with `click import lock
main.click` on the selected Linux environment; keep `main.c` identical to the
frozen example.
