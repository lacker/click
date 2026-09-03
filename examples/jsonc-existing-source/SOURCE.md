# Unchanged json-c source

This project preserves `json_c_version.c` byte-for-byte from the json-c
`json-c-0.17-20230812` release, at the upstream path
`json_c_version.c`:

<https://github.com/json-c/json-c/blob/json-c-0.17-20230812/json_c_version.c>

status: parser-only

The source is intentionally recorded before the C0 frontend can accept it.
The preprocessor/header boundary and the `const char*`/string-valued API are
tracked by [multi-function files, prototypes, and includes](../../issues/multi-function-files-and-headers.md)
and [file-scope objects and string literals](../../issues/global-variables.md).
The source-integrity manifest is checked before the examples gate reports the
expected parser-only result.
