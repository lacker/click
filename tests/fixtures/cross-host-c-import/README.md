# Linux-prepared C import fixture

Ubuntu 24.04 prepared the `main` unit of [`click.project.json`](click.project.json)
with `/usr/bin/gcc`, writing `.click/main/main.c.i` and `click.project.lock.json`.
The C source includes only project-local headers, so the lock's dependencies
are the program's own files; standard interfaces such as `<limits.h>` come
from Click, not from a platform's headers. The lock records the selected
compiler and its ABI probe. The ordinary test relocates these files and
verifies the proof on macOS without that GCC installation.

This is a portability regression for a prepared state. To refresh it, run
`click import lock` in this directory in a selected Linux GCC environment and
commit the project file, lock, and artifact together. Verification hosts only
need the committed files.
