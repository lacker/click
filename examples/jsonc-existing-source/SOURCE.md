# Unchanged json-c source

This project preserves `json_c_version.c` byte-for-byte from the json-c
`json-c-0.17-20230812` release, at the upstream path
`json_c_version.c`:

<https://github.com/json-c/json-c/blob/json-c-0.17-20230812/json_c_version.c>

status: verified

The C implementation, `json_c_version.h`, and `COPYING` are unchanged files
from that same release. `config.h` is a local fixture configuration, not an
upstream file: this translation unit uses none of the feature probes from
upstream `cmake/config.h.in`. The configuration selects ordinary C declarations,
without C++ or MSVC DLL exports. It is not a configuration for the whole library.

The header preprocesses successfully, including its continued numeric
expression, string macro, and export alias. The sidecar proves the numeric
version is 4352 and that the returned string has five readable bytes containing
`0`, `.`, `1`, `7`, and NUL. The source-integrity manifest is checked before
ordinary verification in the examples gate.

The proof is for Click's explicit `x86_64-linux-kernel` target: LP64 with
eight-bit unsigned plain `char`, matching the kernel's `-funsigned-char`
setting. This is a proof of these two unchanged json-c functions under that
configuration, not a proof of the whole library or portability to every target.
The C's `const char *` return type is preserved through parsing and verification.
