# Unchanged json-c source

This project preserves `json_c_version.c` byte-for-byte from the json-c
`json-c-0.17-20230812` release, at the upstream path
`json_c_version.c`:

<https://github.com/json-c/json-c/blob/json-c-0.17-20230812/json_c_version.c>

status: parser-only

The C implementation, `json_c_version.h`, and `COPYING` are unchanged files
from that same release. `config.h` is a local fixture configuration, not an
upstream file: this translation unit uses none of the feature probes from
upstream `cmake/config.h.in`. The configuration selects ordinary C declarations,
without C++ or MSVC DLL exports. It is not a configuration for the whole library.

The header now preprocesses successfully, including its continued numeric
expression, string macro, and export alias. A source-expander regression checks
both return expressions against these exact files. The remaining blocker is
the [plain-char, signed-byte, and const-return model](../../issues/plain-char-string-api.md),
not missing includes. The fixture is **not yet verified**.
The source-integrity manifest is checked before the examples gate reports the
expected parser-only result.
