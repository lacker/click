# Model plain char and signed-byte string APIs

## Violated invariant

The unchanged json-c 0.17 version API cannot be verified even though its header
now preprocesses: `const char *json_c_version(void)` fails with `unsupported C
type char`. Click has unsigned-byte string storage but no signed 8-bit scalar
or pointer model. Both the C and sidecar parsers additionally reject
const-qualified pointer returns; const must be retained through signatures,
calls, and result binding. Aliasing plain char to uint8 would silently impose unsigned
char behavior on signed-char targets. LP64 alone does not determine char
signedness. Do not change upstream C or redefine char in a fixture header.

## Intended regression

Preserve the manifests in `examples/jsonc-existing-source/`. Its exact upstream
header and locally documented config already expand the return expressions to
`"0.17"` and `((0 << 16) | (17 << 8) | 0)`. Prove version number 4352 and a
readable five-byte result containing `0`, `.`, `1`, `7`, and NUL, then promote
the fixture from parser-only to verified.

Also test signed-byte loads, stores, promotion to int, pointer arithmetic,
const preservation, and values above 127. A false unsigned interpretation must
not prove. Include cross-file prototype compatibility and certificate checking.

## Acceptance criteria

- Define the supported plain-char signedness explicitly in the target model.
- Carry signed 8-bit semantics through C parsing, sidecars, lowering, memory,
  integer promotion, and the kernel; preserve distinct C type compatibility
  where char and signed/unsigned char require it.
- Make string literals usable through the real const-char API, without losing
  immutability or byte bounds and without rewriting the preserved C.
- Pass focused regressions and `scripts/check.sh`; update fixture documentation
  only after ordinary verification succeeds.
