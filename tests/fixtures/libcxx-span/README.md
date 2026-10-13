# libc++ `std::span` input closure

`input-closure.tar.gz` holds the headers one translation unit reaches
through `#include <span>` when compiled with libc++ for x86-64 Linux:

- `libcxx/include/` holds LLVM 19.1.7's libc++ headers, from the official
  `LLVM-19.1.7-Linux-X64` release, including the target's `__config_site`.
  `libcxx/include/c++/v1/span` has SHA-256
  `b8b350b8a4992602c184694bee10ac1dc4a7e9412a02988c9e6466972195ba10`.
- `sysroot/usr/include/` holds the glibc headers those reach, from Ubuntu
  noble's `libc6-dev` 2.39-0ubuntu8.9.
- `licenses/` holds libc++'s `LICENSE.TXT` (Apache-2.0 with LLVM
  exceptions) and `libc6-dev`'s copyright file.

The archive was built from the exact `clang++ -std=c++20 -stdlib=libc++ -M`
dependency list of that translation unit, with Clang's resource-directory
headers left out, as `tar --sort=name --mtime=1970-01-01 --owner=0 --group=0
--numeric-owner` piped through `gzip -n -9`. Its SHA-256 is
`eeae6f54e4e25a8a58a5ad503640a9042ff14ee0c15300e7807573e757bdd086`.

`tests/libcxx_span.rs` imports callers of libc++'s `std::span` with the
pinned Clang and checks that Click's standard-library model accessors and
catalog contracts bind the libc++ layout, so the same proofs verify against
libc++ as against libstdc++.
