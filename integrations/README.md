# Upstream integrations

This directory collects bounded verification claims about unchanged source
from other projects. An integration identifies the upstream revision, the
compiler profile Click imports, the `.click` proof, the inputs needed to
reproduce it, and exactly what has been verified. An entry for one function
does not imply support for an entire project or build.

## Verified

- [Bitcoin Core v31.1 `MoneyRange`](bitcoin-core-money-range/README.md): Click
  verifies the unchanged inline function's inclusive monetary range and
  no-write contract, plus four boundary cases, under one pinned Clang C++20
  x86-64 Linux profile. The directory contains the
  [proof sidecar](bitcoin-core-money-range/MoneyRange.click), import
  configuration, source and toolchain provenance, and a hermetic gate fixture.
  It does not claim to verify other Bitcoin Core functions or a binary.

The Linux rbtree work is not yet an upstream integration: its
[model](../examples/rbtree-model/README.md) is verified, but the
[insert example](../examples/rbtree-insert/README.md) explicitly keeps the
unfinished proof as a frontier. A pinned upstream rbtree integration belongs
here when its stated source-level claim is proved and reproducible.
