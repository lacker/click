# Linux-prepared C import fixture

Ubuntu 24.04 prepared `main.i` and the version-2 import lock with `/usr/bin/gcc`.
The C source includes a project-local header and Linux's `<limits.h>`; the
lock records the selected compiler, ABI probe, and opened system headers.
The ordinary test relocates these files and verifies the proof on macOS without
that GCC installation or those Linux headers.

This is a portability regression for a prepared snapshot, not a native
pthread runtime binding. To refresh it, run `click import lock main.click` in
a selected Linux GCC environment and commit the config, lock, and artifact
together. Verification hosts only need the committed files.
